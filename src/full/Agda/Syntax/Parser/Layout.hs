
{-| This module contains the lex actions that handle the layout rules. The way
    it works is that the 'Parser' monad keeps track of a stack of
    'LayoutContext's specifying the indentation of the layout blocks in scope.
    For instance, consider the following incomplete (Haskell) program:

    > f x = x'
    >   where
    >     x' = do y <- foo x; bar ...

    At the @...@ the layout context would be

    > [Layout 12, Layout 4, Layout 0]

    The closest layout block is the one following @do@ which is
    started by token @y@ at column 12.  The second closest block is the
    @where@ clause started by the @x'@ token which has indentation 4.
    Finally, there is a top-level layout block with indentation 0.

    In April 2021 we changed layout handling in the lexer to allow
    stacking of layout keywords on the same line, e.g.:

    > private module M where
    >    postulate A : Set
    >              private
    >                B : Set

    The layout columns in the layout context (stack of layout blocks) can
    have 'LayoutStatus' either 'Tentative' or 'Confirmed'. New layout
    columns following a layout keyword are tentative until we see a new
    line. E.g.

      - The first @private@ block (column 8) is 'Tentative' when we
        encounter the layout keyword @where@.

      - The @postulate@ block (column 12) is 'Tentative' until the newline
        after @A : Set@.

    In contrast,

      - The @module@ block (column 2) is 'Confirmed' from the beginning
        since the first token (@postulate@) after the layout keyword @where@
        is on a new line.

      - The second @private@ block (column 14) is also 'Confirmed' from the
        beginning (for the same reason).

    A new layout column has to be strictly above the last __confirmed__
    column only. E.g., when encountering @postulate@ at column 2 after
    @where@, the confirmed column is still 0, so this is a valid start of
    the block following @where@.

    The column 8 of the @private@ block never enters the 'Confirmed' status
    but remains 'Tentative'. Also, this block can never get more than the
    one declaration it has (@module...@), because when the @module@ block
    closes due to a column \< 2, it closes as well. One could say that
    tentative blocks buried under confirmed blocks are passive, the only
    wait for their closing.

    To implement the process of block confirmation (function
    'confirmLayout'), the lexer has to act on newline characters (except for
    those in a block comment).

      - In ordinary mode, when encountering a newline, we confirm the top
        unconfirmed blocks. Example: The newline after @A : Set@ confirms
        the column 12 after @postulate@. Function: 'confirmLayoutAtNewLine',
        state @bol@.

      - In the @layout@ state following a layout keyword, a newline does not
        confirm any block, but announces that the next block should be
        confirmed from the start. Function: 'confirmedLayoutComing'.

    In order to implement 'confirmedLayoutComing' we have a 'LayoutStatus'
    flag in the parse state (field 'stateLayStatus'). By default, for a new
    layout block, the status is 'Tentative' (unless we saw a newline).

    New layout blocks are created as follows. When a layout keyword is
    encountered, we enter lexer state 'layout' via function 'withLayout'.
    When we exit the 'layout' state via 'newLayoutBlock' with a token that
    marks the new layout column, we push a new 'LayoutBlock' onto the
    'LayoutContext' using the given column and the current 'parseLayStatus'
    which is then reset to 'Tentative'.

    The new block is actually only pushed if the column is above the last
    confirmed layout column ('confirmedLayoutColumn'). If this check fails,
    we instead enter the 'empty_layout' state. This state produces the
    closing brace and is immediately left for 'bol' (beginning of line).

    (Remark: In 'bol' we might confirm some tentative top blocks, but this
    is irrelevant, since they will be closed immediately, given that the
    current token is left of the confirmed column, and tentative columns
    above it must be to the right of this column.)

    The 'offsideRule' (state 'bol') is unchanged. It checks how the first
    token on a new line relates to the top layout column, be it tentative or
    confirmed. (Since we are on a new line, 'Tentative' can only happen when
    we popped some 'Confirmed' columns and continue popping the top
    'Tentative' columns here.) While the token is to the left of the layout
    column, we keep closing blocks.

-}
module Agda.Syntax.Parser.Layout
    ( withLayout
    , offsideRule
    , newLayoutBlock
    , emptyLayout
    , confirmLayout
    ) where

import Control.Monad        ( when )
import Control.Monad.State  ( gets, modify )

import Agda.Syntax.Parser.Lexer
import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Parser.LexActions
import Agda.Syntax.Position

import Agda.Utils.Functor ((<&>))

import Agda.Utils.Impossible

{-| Executed for the first token in each line (see 'Agda.Syntax.Parser.Lexer.bol'),
    except when the last token was a layout keyword.

    Checks the position of the token relative to the current layout context.
    If the token is

    - /to the left/ :
        Exit the current block and a return virtual close brace (stay in the
        'Agda.Syntax.Parser.Lexer.bol' state).

    - /same column/ :
        Exit the 'Agda.Syntax.Parser.Lexer.bol' state and return a virtual semi
        colon.

    - /to the right/ :
        Exit the 'Agda.Syntax.Parser.Lexer.bol' state and continue lexing.

-}
offsideRule :: LexAction Token
offsideRule = LexAction $ \ inp _ _ -> do
    let p = lexPos inp
        i = posToInterval (lexSrcFile inp) p p
    getOffside p >>= \case
        LT  -> do   popBlock
                    return (TokSymbol SymCloseVirtualBrace i)
        EQ  -> do   popLexState
                    return (TokSymbol SymVirtualSemi i)
        GT  -> do   popLexState
                    lexToken


{-| This action is only executed from the 'Agda.Syntax.Parser.Lexer.empty_layout'
    state. It will exit this state, enter the 'Agda.Syntax.Parser.Lexer.bol' state,
    and return a virtual close brace (closing the empty layout block started
    by 'newLayoutBlock').
-}
emptyLayout :: LexAction Token
emptyLayout = LexAction $ \ inp _ _ -> do
    let p = lexPos inp
        i = posToInterval (lexSrcFile inp) p p
    popLexState
    pushLexState bol
    return (TokSymbol SymCloseVirtualBrace i)


{-| Start a new layout block. This is how to get out of the
    'Agda.Syntax.Parser.Lexer.layout' state. There are
    two possibilities:

    - The current token is to the right of the confirmed layout column.

    - The current token is to the left of or in the same column as the confirmed
      layout column.

    In the first case everything is fine and we enter a new layout block at
    the column of the current token. In the second case we have an empty layout
    block so we enter the 'Agda.Syntax.Parser.Lexer.empty_layout' state. In both
    cases we return a virtual open brace without consuming any input.

    Entering a new state when we know we want to generate a virtual @{}@ may
    seem a bit roundabout. The thing is that we can only generate one token at
    a time, so the way to generate two tokens is to generate the first one and
    then enter a state in which the only thing you can do is generate the
    second one.
-}
newLayoutBlock :: LexAction Token
newLayoutBlock = LexAction $ \ inp _ _ -> do
    let p = lexPos inp
        i = posToInterval (lexSrcFile inp) p p
        offset = posCol p
    status   <- popPendingLayout
    kw       <- gets parseLayKw
    prevOffs <- confirmedLayoutColumn <$> getContext
    if prevOffs >= offset
        then pushLexState empty_layout
        else do
            when (status == Confirmed) $
              modifyContext $ confirmTentativeBlocks $ Just offset
            pushBlock $ Layout kw status offset
    return $ TokSymbol SymOpenVirtualBrace i
  where

    -- Get and reset the status of the coming layout block.
    popPendingLayout :: Parser LayoutStatus
    popPendingLayout = do
        status <- gets parseLayStatus
        resetLayoutStatus
        return status

    -- The confirmed layout column, or 0 if there is none.
    confirmedLayoutColumn :: LayoutContext -> Column
    confirmedLayoutColumn = \case
       Layout _ Confirmed c : _   -> c
       Layout _ Tentative _ : cxt -> confirmedLayoutColumn cxt
       [] -> 0 -- should only happen when looking at the first token (top-level layout)

-- | Compute the relative position of a location to the
--   current layout context.
getOffside :: Position' a -> Parser Ordering
getOffside loc =
    getContext <&> \case
        Layout _ _ n : _ -> compare (posCol loc) n
        _                -> GT

-- | At a new line, we confirm either existing tentative layout
--   columns, or, if the last token was a layout keyword, the expected
--   new layout column.
confirmLayout :: Parser ()
confirmLayout = getLexState >>= \ case
  s : _ | s == layout -> confirmedLayoutComing
  _                   -> confirmLayoutAtNewLine
  where

  -- Mark the pending layout block as 'Confirmed'.
  confirmedLayoutComing :: Parser ()
  confirmedLayoutComing = modify $ \ s -> s { parseLayStatus = Confirmed }

  -- Encountering a newline outside of a 'layout' state we confirm top
  -- tentative layout columns.
  confirmLayoutAtNewLine :: Parser ()
  confirmLayoutAtNewLine = modifyContext $ confirmTentativeBlocks Nothing

-- | Confirm all top 'Tentative' layout columns.
-- If a column is given, only those below the given column.
--
-- The code ensures that the newly created 'Definitive' columns
-- are strictly decreasing.
--
confirmTentativeBlocks :: Maybe Column -> LayoutContext -> LayoutContext
confirmTentativeBlocks mcol = \case
    Layout kw Tentative col : cxt | maybe True (col <) mcol
            -> Layout kw Confirmed col : confirmTentativeBlocks (Just col) cxt
    cxt  -> cxt
