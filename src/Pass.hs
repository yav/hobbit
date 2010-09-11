module Pass (Pass, runPass, msg, err, warn, io) where

import UI.ANSI
import System.Exit

import MonadLib

newtype Pass a      = P { unP :: ExceptionT [String] (WriterT [String] IO) a }

instance Monad Pass where
  return            = P . return
  m >>= f           = P (unP m >>= (unP . f))

instance Functor Pass where
  fmap f (P x)      = P (fmap f x)

instance BaseM Pass Pass where
  inBase m          = m

runPass            :: String -> Pass a -> IO a
runPass x (P p)     = do putStrLn (name x) 
                         (r,ws) <- runWriterT (runExceptionT p)
                         mapM_ (putStrLn . warn) ws
                         case r of
                           Left ms  -> do mapM_ (putStrLn . err) ms
                                          exitFailure
                           Right a  -> return a
  where
  err x             = bold (red "Error: ") ++ x
  warn x            = bold (yellow "Warning: ") ++ x 
  name x            = bold (green "*** ") ++ bold (white x)

io                 :: IO a -> Pass a
io m                = P (inBase m)

msg                :: String -> Pass ()
msg x               = P (inBase (putStrLn x))

err                :: [String] -> Pass a
err x               = P (raise x)

warn               :: [String] -> Pass ()
warn x              = P (put x)











