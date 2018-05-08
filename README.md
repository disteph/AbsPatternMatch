# AbsPatternMatch
This is the formalisation, in the proof assistant Coq, of Abstract Pattern-Matching / Abstract Focussing.
The language is described in Part II of the [Habilitation thesis](http://www.lix.polytechnique.fr/~lengrand/Work/HDR/Dissertation/Main.pdf).
The formalisation covers the calculus, its realisability semantics, its abstract machine and the proof of normalisation.
The correspondence with the chapters is given below:

Base file: Basic.v 

Chapter 4: Subsumed by Chapter 5

Chapter 5:

    LAF system (with quantifiers): LAF.v 

Chapter 6:

    Realisability models and Adequacy Lemma: Semantics.v
    LAF system with Eigenvariables: LAFwE.v
    Realisability models with Eigenvariables and Adequacy Lemma: SemanticswE.v 

Chapter 7:

    Normalisation theory: NormalisationTheory.v
    Abstract Machines and Head normalisation: HeadReduction.v
    LAF system with Explicit Label Updates, renamings: LAFwEL.v
    Deriving properties from Non-empty realisability models: SemanticsNE.v 

All the files for the version with quantifiers: First-order.tar.gz 
