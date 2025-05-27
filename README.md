# ◼️🐓 rocq-of-noir

The tool `rocq-of-noir` provides an **open-source and extensive way to formally verify smart contracts written in ⬛&nbsp;Noir**. Formal verification is about checking for any possible input that your code has no security issues, what is essential for code deployed on the blockchain! 🛡️

We rely of the proof assistant [Rocq](https://rocq-prover.org/) to write and verify specifications about your code. We focus in this project in the translation phase from Noir to Rocq and in the definition of a semantics for the language, as well as building blocks to reason about Noir code.

> **If you want to chat about this project or formal verification, you can contact us at [&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;](mailto:&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;) or send a message on our [X account](https://x.com/FormalLand).**

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

## 📝 Example

> Note that this project is still in its early stages. For future evolutions, we are also thinking about adding a compilation from Noir to Rust, so that we can reuse the existing Rust ecosystem to verify the code (for example, using [Kani](https://github.com/model-checking/kani) or our tool [coq-of-rust](https://github.com/formal-land/coq-of-rust)!).

To see an example of verification work, you can look at the `keccak` example in the folder [RocqOfNoir/keccak](RocqOfNoir/keccak). We make our proofs for the beginning of the Keccak function, showing the handling of one `for` loop which we represent as a "fold" on the Rocq side.

In general, our proof technique is as follows:

1. Show that the monomorphized code is correct is equivalent to a polymorphic form where we keep the generic types. This removes the duplication of some functions, and makes sure that names are more stable (no more generated indexes to distinguish between the various function instanciations).
2. Show that the polymorphic code is equivalent to a purely functional definition applying the semantic rules defined in [RocqOfNoir/proof/RocqOfNoir.v](RocqOfNoir/proof/RocqOfNoir.v).
3. Express and prove properties using the usual techniques on functional and monadic Rocq code!

Depending on the specificities of your code, we can also design techniques which are more specific and more efficient.

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
