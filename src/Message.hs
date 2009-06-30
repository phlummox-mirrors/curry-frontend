-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- Message - A library for dealing with compiler messages
--
-- Note: This module overwrites the functions declared in "Message"
--                
-- January 2006,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module Message where

import Curry.Base.Position

--import Control.Monad.Error
--import Control.Monad.Writer

--type MsgMonad = ErrorT String (Writer [Message])

--emitWarning :: Position -> WarningType -> MsgMonad ()
--emitWarning p w = tell (Message (Warning w) (Just p) (warnMsg w))


-------------------------------------------------------------------------------

-- Type for representing compiler messages (currently errors and warnings)
data Message = Message MessageType (Maybe Position) String

-- Data type for representing available compiler message types
data MessageType = Warning WarningType | Error deriving Eq

-- the different warnings are categorized by WarningType
data WarningType = UnrefTypeVar
                 | UnrefVar
                 | ShadowingVar
                 | IdleCaseAlt
                 | OverlapCase
                 | OverlapRules
                 | RulesNotTogether
                 | MultipleImportModule
                 | MultipleImportSymbol
                 | MultipleHiding 
                 deriving Eq

-- An instance of Show for converting messages to readable strings
instance Show Message where
 show (Message (Warning _) mpos msg) = showMessage "Warning" mpos msg
 show (Message Error   mpos msg) = showMessage "ERROR" mpos msg


-------------------------------------------------------------------------------

--
message :: MessageType -> Position -> String -> Message
message mtype pos msg = Message mtype (Just pos) msg

--
message_ :: MessageType -> String -> Message
message_ mtype msg = Message mtype Nothing msg

--
countMessages :: MessageType -> [Message] -> Int
countMessages mtype msgs = length (filter (((==) mtype) . messageType) msgs)

--
messageType :: Message -> MessageType
messageType (Message mtype _ _) = mtype


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
showMessage :: String -> (Maybe Position) -> String -> String
showMessage what mpos msg
   = what ++ ": " ++ pos ++ msg
 where
 pos = maybe "" (\p -> show p ++ ": ") mpos


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------