# ◼️🐓 coq-of-noir

With `coq-of-noir`, we provide an **open-source and extensive way to formally verify smart contracts written in ⬛&nbsp;Noir**. Formal verification is about checking for any possible input that your code has no security issues, what is essential for code deployed on the blockchain! 🛡️

To keep things simple, we rely on the well-known proof assistant [Rocq](https://rocq-prover.org/) for all the verification work: if you are already knowledgeable into this system, you can readily use `coq-of-noir` to verify your smart contracts!

## 🏎️ Getting Started

Follow what we do in our CI file [coq.yml](.github/workflows/coq.yml). Sorry for not having the time to provide more explanations!

## ✅ What Works

The following steps work:

- A generated translation of the `base64` library of Noir to Coq in a code that compiles; we should thus support a large part of the Noir language.
- Semantics rules to reason on code like the above together with a proof strategy. This should already cover most of the Noir language.
- A formally verified functional specification of one of the functions with a loop from the `base64` library, exercising mutations and array access. We consider this to be our main test to see that `coq-of-noir` can work on non-trivial examples.

Note that the proof process is still very verbose, and this tool is still a work in progress. Contact us at [&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;](mailto:&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;) or by direct message on our [X account](https://x.com/FormalLand) if you are interested.

## 🔭 Goal and Vision

The goal is to enable each team developing critical applications (meaning handling user money) to verify the correctness of their code with the higest degree of certainty thanks to **formal verification**.

For those who do not know, formal verification is a technique to verify software for 100% of possible execution parameters. **This means that the code cannot have bugs or vulnerabilities!** Initially applied to software from the spacial/defense industry, the key idea is to mathematically reason about the code to talk about possibly infinitely many possible cases, and to verify all the reasoning by a dedicated tool called a proof checker, in our case 🐓&nbsp;Coq.

In this repository, we provide a command to automatically translate a Noir program to a representation in Coq. We translate the code after the monomorphisation phase of the Noir compiler so that we do not have to deal with polymorphism or type classes. Instead, one can reconstruct this organization of the code on the Coq side in a refinement step, if needed.

This translation is a shallow embedding optimized to write specifications and proofs about the code. As we erase all the types during the translation to keep only the values, we recommend doing a first proof step that reconstructs these types. This first proof step is also an opportunity to explicit the structure of the global state.

Our initial target is to verify a part of the [base64](https://github.com/noir-lang/noir_base64), which uses field arithmetic for optimizations. It also includes many loops, which are generally non-trivial to fully verify with formal verification.

_If you have a Noir project that you want to formally verify, either start using `coq-of-noir` or contact us!_

## 📚 Blog posts

Here are some blog posts featuring this tool:

- [◼️ A formal verification tool for Noir – 1](https://formal.land/blog/2024/11/01/tool-for-noir-1)
- [◼️ A formal verification tool for Noir – 2](https://formal.land/blog/2024/11/15/tool-for-noir-2)

## ⚖️ License

`coq-of-noir` is free and **open source**. It is distributed under a dual license. (MIT/APACHE) The translation phase is based on the code of the Noir compiler to maximize code reuse.
