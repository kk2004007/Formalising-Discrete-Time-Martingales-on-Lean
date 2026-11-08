# PROJECT 1 Formalisation of Discrete Time Martingale Theory

In this file we introduce discrete time martingales and formalise
the Martingale Transform Theorem

## Main results
- `martingales`: a construction of a `martingales`, given a `filtration` and a `Measure`.
- `martingaleransform` : the product of a  `previsible` process and an `adapted` process.
- `martingaletransformtheorem`: the main transform theorem of martingales

## Notation

 - `Ω` : Sample Space.
 - `ω` : Elements of Sample Space / Events
 - `m`, `𝓕`: Measurable Spaces/ σ-algebras over `Ω`
 - `X`, `H` : Processes on the measurable spaces `m` and `𝓕`,
 usually martingales and previsible process respectively
 - `μ` : Measure over `m` and `𝓕`,
 usually refers to Expectation and Conditional Expectation

## References
* https://leansearch.net/?q=measure+theory
* Mathlib4 GitHub
* https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/
