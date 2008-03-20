
module IO.File where

open import Base
open import IO

{-# IMPORT System.IO #-}

FilePath = String

data IOMode : Set where
  readMode      : IOMode
  writeMode     : IOMode
  appendMode    : IOMode
  readWriteMode : IOMode

{-# COMPILED_DATA IOMode ReadMode WriteMode AppendMode ReadWriteMode #-}

canRead : IOMode -> Bool
canRead readMode      = true
canRead writeMode     = false
canRead appendMode    = false
canRead readWriteMode = true

canWrite : IOMode -> Bool
canWrite readMode      = false
canWrite writeMode     = true
canWrite appendMode    = true
canWrite readWriteMode = true

CanRead : IOMode -> Set
CanRead m = IsTrue (canRead m)

CanWrite : IOMode -> Set
CanWrite m = IsTrue (canWrite m)

postulate
  Handle : Set

private
 postulate
  hs-openFile : FilePath -> IOMode -> IO Handle
  hs-hClose   : Handle -> IO Unit

  hs-hGetChar : Handle -> IO Char
  hs-hGetLine : Handle -> IO String
  hs-hGetContents : Handle -> IO String

  hs-hPutStr  : Handle -> String -> IO Unit

{-# COMPILED hs-openFile     openFile #-}
{-# COMPILED hs-hClose       hClose #-}
{-# COMPILED hs-hGetChar     hGetChar #-}
{-# COMPILED hs-hGetLine     hGetLine #-}
{-# COMPILED hs-hGetContents hGetContents #-}
{-# COMPILED hs-hPutStr      hPutStr #-}

Handles = List (Handle × IOMode)

abstract
 -- The FileIO monad. Records the list of open handles before and after
 -- a computation. The open handles after the computation may depend on
 -- the computed value.
 data FileIO (A : Set)(hs₁ : Handles)(hs₂ : A -> Handles) : Set where
   fileIO : IO A -> FileIO A hs₁ hs₂

private
 abstract
  unFileIO : forall {A hs f} -> FileIO A hs f -> IO A
  unFileIO (fileIO io) = io

FileIO₋ : Set -> Handles -> Handles -> Set
FileIO₋ A hs₁ hs₂ = FileIO A hs₁ (\_ -> hs₂)

abstract
  openFile : {hs : Handles} -> FilePath -> (m : IOMode) ->
             FileIO Handle hs (\h -> (h , m) :: hs)
  openFile file mode = fileIO (hs-openFile file mode)

infix 30 _∈_
data _∈_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs} -> x ∈ x :: xs
  tl : forall {y xs} -> x ∈ xs -> x ∈ y :: xs

delete : {A : Set}{x : A}(xs : List A) -> x ∈ xs -> List A
delete [] ()
delete (x :: xs)  hd    = xs
delete (x :: xs) (tl p) = x :: delete xs p

abstract
  hClose : {hs : Handles}{m : IOMode}(h : Handle)(p : (h , m) ∈ hs) ->
           FileIO₋ Unit hs (delete hs p)
  hClose h _ = fileIO (hs-hClose h)

  hGetLine : {hs : Handles}{m : IOMode}{isRead : CanRead m}(h : Handle)
             (p : (h , m) ∈ hs) -> FileIO₋ String hs hs
  hGetLine h _ = fileIO (hs-hGetLine h)

  hGetContents : {hs : Handles}{m : IOMode}{isRead : CanRead m}(h : Handle)
             (p : (h , m) ∈ hs) -> FileIO₋ String hs (delete hs p)
  hGetContents h _ = fileIO (hs-hGetContents h)

abstract
  -- You can only run file computations that don't leave any open
  -- handles.
  runFileIO : {A : Set} -> FileIO₋ A [] [] -> IO A
  runFileIO (fileIO m) = m

abstract
  _>>=_ : forall {A B hs f g} ->
          FileIO A hs f -> ((x : A) -> FileIO B (f x) g) -> FileIO B hs g
  fileIO m >>= k = fileIO (bindIO m \x -> unFileIO (k x))

  return : forall {A hs} -> A -> FileIO₋ A hs hs
  return x = fileIO (returnIO x)
