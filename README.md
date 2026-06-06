# FinalProject

This is the code repository for my Math 157 Final project.

My original project was to be a graph theory theorem but I had a lot of difficulty in formalizing
the proof not using certrain mathlib theorems. The use of these theorems made the proofs trivial but
proving these theorems from scratch was very difficult and would take a lot more time than I have to
complete the project so I decided to pivot to a theorem that I have some more experience with
proving from scratch.

Included in this project are helper theorems and lemmas that are necessary for the formalization of the proof, as well as custom defintions for different mathematical concepts relevant to this project.
The backwards direction of this proof takes a different strategy than Ross though. Ross uses limit
infimum and limit supremum in his proof which would require lots of background formalization from
scratch. So, I decided to formalize the Cauchy → Convergent direction using the Bolzano Wierstrass
Theorem. I have left this as a black box axiomly since it is a nontrivial proof using a 'peak'
argument in the textbook.

## References

1. Kenneth A. Ross, Elementary Analysis: The Theory of Calculus, Springer, 2013.
   - This text was used for proof strategies and various theorems for the formalization of the proof
2. Math 157 Lectures.
3. Math 157 Discussion Handouts.
4. Mathematics in Lean, Lean Prover Community.
5. Lean Language Reference Manual.
6. Mathlib4 Documentation.
7. Theorem Proving in Lean 4.
   - These were used for syntax and tactics for lean and theorem names in mathlib
8. Bolzano–Weierstrass theorem 
   - Standard real analysis result; not formalized in this project, taken as an axiom based on Ross and UCSD coursework
  
In addition to the above sources, I used ChatGPT (OpenAI) as an AI-assisted programming and learning tool. It was primarily used for:

1. Debugging Lean 4 compilation and type-checking errors including issues related to imports, project setup (e.g, lake build system), and tactic failures.
2. Clarifying Lean syntax and Mathlib usage such as how to show a set in lean is nonempty and the syntax for Finset.range
3. Helping interpret error messages and suggest possible fixes such as type mismatches

All final mathematical decisions, proofs, and formalizations were independently verified and implemented in Lean 4.