Modulübersicht curry-frontend
=============================

  * `Base`: Grundlegende Typen und Funktionen
      * `.CurryTypes` : Konvertierung der Typrepräsentation aus
                        `Curry.Syntax.Type` in die aus `Base.Types`
      * `.Expr`       : Typklassem zur Berechnung von freien und gebundenen
                        Variablen
      * `.Messages`   : Darstellung von Fehlermeldungen
      * `.NestEnv`    : Geschachtelte Umgebungen
      * `.OldScopeEnv`:
      * `.SCC`        : Berechnung streng zusammenhängender Komponenten
      * `.ScopeEnv`   :
      * `.Subst`      : Implementierung von Substitutionen
      * `.TopEnv`     : Top-Level Umgebung
      * `.Types`      : interne Repräsentation von Typen
      * `.TypeSubst`  : Typsubstitutionen
      * `.Typing`     : Typberechnung
      * `.Utils`      : Hilfsfunktionen
  * `Checks`: Überprüfungen eines Curry-Moduls
      * `.ExportCheck`: Überprüfung der Exports (unbekannte Symbole etc.)
      * `.KindCheck`  : Überprüfung der Typkonstruktoren, Unterscheidung von
                        Typkonstruktoren und Variablen
      * `.PrecCheck`  : Umordnung des Syntaxbaumes entsprechend der
                        Operatorpräzedenzen
      * `.SyntaxCheck`: Überprüfung der Syntax, Umbenennung von Variablen
      * `.TypeCheck`  : Typüberprüfung
      * `.WarnCheck`  : Erzeugung von Warnungen
  * `Env`: Umgebungen für die Kompilierung
      * `.Eval`           : Auswertungsannotationen
      * `.Interface`      : Importierte Interfaces
      * `.ModuleAlias`    : Aliase für Module
      * `.OpPrec`         : Operatorpräzedenzen
      * `.TypeConstructor`: Typkonstruktoren
      * `.Value`          : Werte (Funktionen, Konstruktoren, Labels)
  * `Files.CymakePath`: Pfad zur binary
  * `Generators`: Generatoren zur Code-Erzeugung
      * `GenAbstractCurry`: Erzeugung von AbstractCurry
      * `GenFlatCurry`    : Erzeugung von FlatCurry
  * `Html`: Dokumentation
      * `.CurrryHtml`    : Erzeugung einer HTML-Dokumentation
      * `.SyntaxColoring`: Hilfsfunktionen
  * `IL`: interne Zwischensprache (Intermediate Language)
      * `.Pretty`: Pretty-Printer für die Intermediate Language
      * `.Type`  : Intermediate Language
      * `.XML`   : XML-Darstellung der Intermediate Language
  * `Transformations`: Codetransformationen
      * `.CaseCompletion`: Vervollständigung von case-Ausdrücken
      * `.CurryToIL`     : Übersetzung von Curry in die Intermediate Language
      * `.Desugar`       : Übersetzung von syntaktischem Zucker
      * `.Lift`          : Lifting von lambda-Ausdrücken und lokalen Funktionen
      * `.Qual`          : Qualifizierung von Konstruktoren und Funktionen
      * `.Simplify`      : Code-Vereinfachung
  * `CompilerEnv`   : Sammlung von Informationen für die Kompilierung eines
                      Moduls
  * `CompilerOpts`  : Optionen für den Compiler
  * `CurryBuilder`  : Kompilierung eines Moduls inklusive Modulabhängigkeiten
  * `CurryDeps`     : Berechnung von Modulabhängigkeiten
  * `cymake`        : Command-line tool
  * `Exports`       : Erzeugung des Interfaces
  * `Frontend`      : API-Modul (to be removed)
  * `Imports`       : Import von Funktionen etc. aus Schnittstellen
  * `Interfaces`    : Laden der benötigten Schnittstellen
  * `Modules`       : Kompilierung eines einzelnen Moduls
  * `ModuleSummary` : Zusammenfassung eines Moduls (to be removed)
