
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
    started by token @foo@ at column 12.  The second closest block is the
    @where@ clause started by the @x'@ token which has indentation 4.
    Finally, there is a top-level layout block with indentation 0.

-}
module Agda.Syntax.Parser.Layout
    ( withLayout
    , offsideRule
    , newLayoutBlock
    , emptyLayout
    , confirmLayout
    -- , confirmLayoutAtNewLine, confirmedLayoutComing
    ) where

import Debug.Trace
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
offsideRule inp _ _ =
    do  offs <- getOffside p
        case offs of
            LT  -> do   popBlock
                        return (TokSymbol SymCloseVirtualBrace i)
            EQ  -> do   popLexState
                        return (TokSymbol SymVirtualSemi i)
            GT  -> do   popLexState
                        lexToken
    where
        p = lexPos inp
        i = posToInterval (lexSrcFile inp) p p


{-| This action is only executed from the 'Agda.Syntax.Parser.Lexer.empty_layout'
    state. It will exit this state, enter the 'Agda.Syntax.Parser.Lexer.bol' state,
    and return a virtual close brace (closing the empty layout block started
    by 'newLayoutBlock').
-}
emptyLayout :: LexAction Token
emptyLayout inp _ _ =
    do  popLexState
        pushLexState bol
        return (TokSymbol SymCloseVirtualBrace i)
    where
        p = lexPos inp
        i = posToInterval (lexSrcFile inp) p p


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
newLayoutBlock inp _ _ = do
    status   <- popPendingLayout
    prevOffs <- confirmedLayoutColumn <$> getContext
    if prevOffs >= offset
        then pushLexState empty_layout
        else do
            when (status == Confirmed) $
              modifyContext $ confirmTentativeBlocks $ Just offset
            pushBlock $ Layout status offset
    return $ TokSymbol SymOpenVirtualBrace i
  where
    p = lexPos inp
    i = posToInterval (lexSrcFile inp) p p
    offset = posCol p

    -- | Get and reset the status of the coming layout block.
    popPendingLayout :: Parser LayoutStatus
    popPendingLayout = do
        status <- gets parseLayStatus
        resetLayoutStatus
        return status

    -- | The confirmed layout column, or 0 if there is none.
    confirmedLayoutColumn :: LayoutContext -> Column
    confirmedLayoutColumn = \case
       Layout Confirmed c : _   -> c
       Layout Tentative _ : cxt -> confirmedLayoutColumn cxt
       [] -> 0

-- | Compute the relative position of a location to the
--   current layout context.
getOffside :: Position' a -> Parser Ordering
getOffside loc =
    getContext <&> \case
        Layout _ n : _ -> compare (posCol loc) n
        _              -> GT


confirmLayout :: Parser ()
confirmLayout = getLexState >>= \ case
  s : _ | s == layout -> confirmedLayoutComing
  _                   -> confirmLayoutAtNewLine
  where

  -- | Mark the pending layout block as 'Confirmed'.
  confirmedLayoutComing :: Parser ()
  confirmedLayoutComing = modify $ \ s -> s { parseLayStatus = Confirmed }

  -- | Encountering a newline outside of a @layout_@ state we confirm top
  --   tentative layout columns.
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
    Layout Tentative col : cxt | maybe True (col <) mcol
            -> Layout Confirmed col : confirmTentativeBlocks (Just col) cxt
    cxt  -> cxt
