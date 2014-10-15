Change log for curry-frontend
=============================

Under development
=================

  * Replaced MessageM monad with CYT monads and moved CYT monads to curry-base

  * Implemented warnings for overlapping module aliases - fixes #14

  * The check for overlapping rules has been completely refactored and
    improved to now also handle rigid case expressions.

  * The check for missing pattern matching alternatives now correctly handles
    String literals - fixes #1048.

  * Added warnings for top-level functions without type signatures - fixes #769

  * Moved pretty-printing of types from Checks.TypeCheck to Base.CurryTypes

  * Type synonyms in typed expressions are now desugared - fixes #921

  * Declaration of operator precedence is now optional in infix operator
    declarations

  * Moved module `InterfaceEquivalence` to curry-base
    (`Curry.Syntax.InterfaceEquivalence`)

  * Converted literate Haskell files into simple Haskell files

  * Removed support for FlatCurry XML files.

  * Added syntax extension `NegativeLiterals` to translate negated literals
    into negative literals instead of a call to `Prelude.negate` and
    `Prelude.negateFloat`, respectively.

  * The frontend now considers options pragmas of the following form:

    ~~~ {.curry}
    {-# OPTIONS_CYMAKE opt1 ... optn #-}
    ~~~

    The string following `OPTIONS_CYMAKE` will be split at white spaces
    and treated like an ordinary command line argument string.

    If one wishes to provide options containing spaces, e.g., directory
    paths or alike, this can be achieved by quoting the respective argument
    using either `'single quotes'` or `'double quotes'` (may bot be mixed).

    Note that *following options are excluded*:

      * A change of the current mode
        (e.g., change from compilation to HTML generation)
      * A change of the import  paths
      * A change of the library paths
      * A change of the compilation targets
        (e.g., change from FlatCurry to AbstractCurry)

    These options can only be set via the command line.

  * Refactored the source code HTML generation.
    The generation now supports full Curry with all supported extensions,
    i.e., it supports pragmas, record types and functional patterns.
    Furthermore, the created HTML has been simplified, and updated towards
    HTML 5.

  * The HTML generation now accepts an option `--htmldir=dir` to specify
    the output directory of the generated HTML files.

Version 0.3.10
==============

  * Various improvements of the internal structure.

  * Improved status messages. The compilation status message are now of the form

        [m of n] Compiling/Skipping <Module> (<source file>, <target file>)

  * Implemented support for custom preprocessors. It is now possible to run
    a custom preprocessor command via the following options:

    * `-F` enables support for a preprocessor
    * `-pgmF <cmd>` set the preprocessor command to `<cmd>`
    * `-optF <arg>` adds an additional argument to the preprocessor command
      (can be repeated to add multiple arguments)

    The preprocessor is applied to all source files which are (re)compiled
    after unliterating *and after determining the import list*.
    Consequently, adding modules via the preprocessor will results in
    compilation errors due to missing imports.
    On the other hand, the frontend will automatically determine changed
    files which are then handed to the preprocessor.

    The command is called with at least three arguments:

     #. The (normalised) file name of the source file currently processed.
        **This name is intended only for reference.**
     #. The name of the file containing the (potentially unliterated)
        contents of the original file.
        **This is the file the preprocessor should read from.**
     #. The name of the file where the preprocessed source code should go to.
        **This is the file the preprocessor should write to.**
     #. Optionally, any additional arguments specified using `-optF`.

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

