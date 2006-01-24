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

import Position


-------------------------------------------------------------------------------

-- Type for representing compiler messages (currently errors and warnings)
data Message = Message MessageType (Maybe Position) String

-- Data type for representing available compiler message types
data MessageType = Warning  | Error deriving Eq


-- An instance of Show for converting messages to readable strings
instance Show Message where
 show (Message Warning mpos msg) = showMessage "Warning" mpos msg
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