# mrm
Modular Reifiable Matching, A List-of-Functors Approach to Two-Level Types

Modular Reifiable Matching (MRM) is a new approach to two level types using a
*fixpoint of list-of-functors* representation. MRM allows the modular definition
of datatypes and functions by pattern matching, using a style similar to the
widely popular Datatypes à la Carte (DTC) approach. However, unlike DTC, which
uses the more conventional two-level types approach using fixpoints of functors,
MRM uses a fixpoint of *list-of-functors*.

This approach has advantages that
help with various aspects of extensibility, modularity and
reuse. Firstly, modular pattern matching definitions are collected
using a list of matches that is fully reifiable. This
allows for extensible pattern matching definitions to be easily
reused/inherited, and particular matches to be overridden. Such
flexibility is used, among other things, to implement
*extensible generic traversals*.

Secondly, the subtyping relation between lists of functors is quite simple,
does not require backtracking, and is easy to model in languages
like Haskell.

This repository implements MRM as a Haskell library, and illustrates
its use and applicability through some examples.

More details of MRM can be found in 
Bruno C. d. S. Oliveira, Shin-Cheng Mu, and Shu-Hung You.
[Modular reifiable matching: a list-of-functors approach to two-level types](http://www.iis.sinica.edu.tw/~scm/pub/mrm.pdf).
In the 8th ACM SIGPLAN Symposium on Haskell (Haskell 2015), pages 82-93. Sep. 2015.
