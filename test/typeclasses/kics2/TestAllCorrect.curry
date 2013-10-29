
import TestDeriving1
import TestDeriving2
import TestDerivingBounded
import TestDerivingEnum
import TestEnumerations
import TestList
import TestPrelude
import TestShow
import TestNumbers

allTests = [ TestDeriving1.allCorrect
           , TestDeriving2.allCorrect
           , TestDerivingBounded.allCorrect
           , TestDerivingEnum.allCorrect
           , TestEnumerations.allCorrect
           , TestList.allCorrect
           , TestPrelude.allCorrect
           , TestShow.allCorrect
           , TestNumbers.allCorrect
           ]

allCorrect = and allTests