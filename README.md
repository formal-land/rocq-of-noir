# ◼️🐓 rocq-of-noir

The tool `rocq-of-noir` provides an **open-source and extensive way to formally verify smart contracts written in ⬛&nbsp;Noir**. Formal verification is about checking for any possible input that your code has no security issues, what is essential for code deployed on the blockchain! 🛡️

To keep things simple, we rely on the well-known proof assistant [Rocq](https://rocq-prover.org/) for all the verification work: if you are already knowledgeable into this system, you can readily use `rocq-of-noir` to verify your smart contracts!

## 🏎️ Getting Started

1. Install the `rocq-of-noir` fork of the Noir compiler:
  ```sh
  cargo install --path tooling/nargo_cli
  ```

2. Translate an example to JSON representation. Here, we translate the test for the Keccak hash function, which includes the code of the hash function itself:
  ```sh
  cd noir_stdlib
  nargo test hash::keccak::tests::smoke_test --show-monomorphized
  cd ..
  ```
  Note that the translation to JSON is what our fork of the Noir compiler provides. This is the AST of the code after the monomorphization phase.

3. Translate the JSON representation to Rocq:
  ```sh
  python scripts/rocq_of_noir.py noir_stdlib/monomorphized_program.json >RocqOfNoir/keccak_monomorphic.v
  ```
  The file `RocqOfNoir/keccak_monomorphic.v` is the Rocq representation of the Noir code!

4. Compile the Rocq code:
  ```sh
  cd RocqOfNoir
  make
  ```

To see an example of verification work, you can look at the `base64` example in the folder [RocqOfNoir/base64](RocqOfNoir/base64). We follow these steps:

- Show that the monomorphized code is correct is equivalent to a polymorphic form where we keep the generic types. This removes the duplication of some functions, and makes sure that names are more stable (no more generated indexes to distinguish between the various function instanciations).
- Show that the polymorphic code is equivalent to a purely functional definition applying the semantic rules defined in [RocqOfNoir/proof/RocqOfNoir.v](RocqOfNoir/proof/RocqOfNoir.v).
- Express and prove properties using the usual techniques on functional and monadic Rocq code!

## ✅ What Works

The following functionalities are currently implemented:

- **Translation:** Automatic translation of Noir programs to a representation in Rocq.
- **Semantics:** Formal semantics for reasoning about the translated Noir code.
- **Proof Strategy:** A proof strategy to formally verify properties of Noir programs.
- **Verified Example:** A verified functional specification of a non-trivial example (base64 loop) demonstrating mutation and array access handling.

Contact us at [&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;](mailto:&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;) or by direct message on our [X account](https://x.com/FormalLand) if you are interested.

## 🔭 Goal and Vision

The goal is to enable each team developing critical applications (meaning handling user money) to verify the correctness of their code with the higest degree of certainty thanks to **formal verification**.

For those who do not know, formal verification is a technique to verify software for 100% of possible execution parameters. **This means that the code cannot have bugs or vulnerabilities!** Initially applied to software from the spacial/defense industry, the key idea is to mathematically reason about the code to talk about possibly infinitely many possible cases, and to verify all the reasoning by a dedicated tool called a proof checker, in our case 🐓&nbsp;Rocq.

In this repository, we provide a command to automatically translate a Noir program to a representation in Rocq. We translate the code after the monomorphisation phase of the Noir compiler so that we do not have to deal with polymorphism or type classes. Instead, one can reconstruct this organization of the code on the Rocq side in a refinement step, if needed.

This translation is a shallow embedding optimized to write specifications and proofs about the code. As we erase all the types during the translation to keep only the values, we recommend doing a first proof step that reconstructs these types. This first proof step is also an opportunity to explicit the structure of the global state.

Our initial target is to verify a part of the [base64](https://github.com/noir-lang/noir_base64), which uses field arithmetic for optimizations. It also includes many loops, which are generally non-trivial to fully verify with formal verification.

_If you have a Noir project that you want to formally verify, either start using `rocq-of-noir` or contact us!_

## 📚 Blog posts

Here are some blog posts featuring this tool:

- [◼️ A formal verification tool for Noir – 1](https://formal.land/blog/2024/11/01/tool-for-noir-1)
- [◼️ A formal verification tool for Noir – 2](https://formal.land/blog/2024/11/15/tool-for-noir-2)

## ⚖️ License

`rocq-of-noir` is free and **open source**. It is distributed under a dual license. (MIT/APACHE) The translation phase is based on the code of the Noir compiler to maximize code reuse.
