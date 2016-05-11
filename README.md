Ben Sherman
Final Project: Formal proofs of asymptotic cryptographic properties
6.875 : Cryptography


How to "run" the Coq code
===========================================

The file `CSD.v` is the Coq code which contains my definitions as well
as theorems and proofs. One can read the source code to learn about these
definitions and see what has been proved.

Additionally, it is also possible to load the file in Coq. This allows one to
1) Check that definitions typecheck, and that the proofs of theorems are valid.
2) Execute definitions (and theorems!) as one would in a conventional
   interpreter for a programming language
3) Interactively inspect proofs to see how the proof was accomplished.

To run the Coq code, follow the following steps:
- Install Coq v8.4pl6. See https://coq.inria.fr/coq-84.
  Note that Coq v8.4pl6 is *not* the most recent version of Coq,
  so take special care to install this version.
  Download the version which has CoqIDE bundled with it.
- Download and compile the Foundational Cryptography Framework:
  https://github.com/adampetcher/fcf
- Modify the `_CoqProject` file to point to the correct filepath
  that points to wherever you downloaded the Foundational Cryptography
  Framework.
- Open `CSD.v` in CoqIDE. At this point, you can interactively step through
  the code and proofs.
