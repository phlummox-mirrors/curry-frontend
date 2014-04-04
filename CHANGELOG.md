Change log for curry-frontend
=============================

Version 0.3.9
=============

  * Simplified verbosity options by merging options "-v1" and "-v2".
    Now only "-v0" and "-v1" are supported.

  * Fixed bug in non-exhaustive pattern matching check which occured
    when retrieving the siblings of a constructor imported using an alias.

  * Fixed bug when using functional patterns in `case`-expressions.
    Functional patterns are only allowed in the patterns of a function
    definition and forbidden elsewhere, i.e., in `case`-expressions,
    `do`-sequences, list comprehensions or lambda expressions.

  * Implementation of module pragmas added. Module pragmas of the following
    types are now parsed and represented in the abstract syntax tree:

    ~~~ {.curry}
    {-# LANGUAGE LANG_EXT+ #-}
    {-# OPTIONS "string" #-}
    {-# OPTIONS_TOOL "string" #-}
    module Main where
    ~~~

    where

      - `LANGEXT+` is a non-empty, comma-separated list of the following
        language extensions: `AnonFreeVars`, `FunctionalPatterns`,
        `NoImplicitPrelude`, `Records`
      - `TOOL` is either `KICS2`, `PAKCS`, or some other tool, represented
        as `Unknown String`.

    While the distinct language pragmas enable the respective language
    extensions, the OPTIONS pragma is ignored.

    All other texts given in the pragma braces is ignored and treated as
    a nested comment.

  * Error message for different arities of function equations now also
    report the corresponding source code positions.

Version 0.3.8
=============

  * Implemented warnings for non-exhaustive pattern matchings
    both in function declarations and `case`-expressions - fixes #349.

  * Extended options to enable/disable certain types of warnings.

  * Fixed problem when defining an operator directly after an import statement
    without import restrictions - fixes #494.

  * Fixed bug w.r.t. polymorphically typed local variables - fixes #480.

  * Fixed missing polymorphism in record labels - fixes #445.

  * Dumping of intermediate structures improved.

  * Fixed bug in type checking w.r.t. recursive type synonyms - fixes 489.

  * Reactivation of Curry interface files.
    During adaption of the MCC frontend to FlatCurry the Curry interface
    files have been deactivated and replaced by FlatCurry's interface
    files. To allow the later addition of type classes to Curry,
    they have now been reactivated.

  * Implemented missing semantics of functional patterns in combination
    with non-linear left-hand-sides and as-patterns.

  * Various improvements.

Version 0.3.7
=============

  * Support for typed FlatCurry expressions added. Now additional type
    information given by the programmer as in

    ~~~ {.curry}
    null (unknown :: [()])
    ~~~

    is represented in FlatCurry and cann therefore be processed by other
    programs like PAKCS or KICS2.

Version 0.3.6
=============

  * Error messages are now sorted according to their source code position.

Version 0.3.5
=============

  * Improved reporting of mutiple type signatures.

Version 0.3.4
=============

  * Bug in renaming phase fixed.

Version 0.3.3
=============

  * Corrected translation of `fcase`-expressions.

Version 0.3.2
=============

  * Non-linear left-hand-sides now work with guarded expressions - fixes #328.

  * Implemented precedence check - fixes #327.

  * Case completion refactored and corrected - fixes #323.

  * Various improvements and refactorings.

Version 0.3.1
=============

  * Corrected renaming of anonymous free variables - fixes #288.

Version 0.3.0
=============

  * Massive refactoring of the previous version.

  * All compiler warnings removed.

  * Fixed various implementation bugs (#9, #16, #19, #29, #289).

