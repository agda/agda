
module GUILib where

class Widget w where

setVisible :: Widget w => w -> Bool -> IO ()
setVisible w _ = return ()

data Window = Window

instance Widget Window where

newWindow :: IO Window
newWindow = return Window

