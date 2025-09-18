# TensorRight

TensorRight is an automatic tool to verify tensor graph rewrites for tensors of arbitrary ranks and sizes.
Tensor Graph Rewriting is one of the key optimizations in Tensor Compilers such as [XLA](https://github.com/openxla/xla).

## Key Features of TensorRight

- We introduce a core language, TensorRight DSL, to represent complex tensor graph rewrites with preconditions.
- TensorRight DSL uses a novel axis definition, called _aggregated-axis_, which allows reasoning about an arbitrary number of dimensions.
- TensorRight provides operator specifications that closely resemble [XLA-HLO](https://openxla.org/xla/operation_semantics).
TensorRight implements the denotational semantics for these operators.
- TensorRight presents an automatic verification strategy to verify tensor graph rewrites in the unbounded setting, i.e, for arbitrary ranks and sizes, by inferring a bound on aggregated-axis ranks, such that verifying the rewrite for all ranks within the bound implies correctness in the unbounded setting. <br>
Hence, TensorRight converts the _unbounded-verification_ proof obligation to a finite set of _bounded-verification_ proof obligations, which are then dispatched to an SMT solver using symbolic execution to automatically verify rewrite rules.
- TensorRight is implemented in Haskell and uses [Grisette](https://github.com/lsrcz/grisette) as the symbolic evaluation engine.
TensorRight can successfully represent 121 of the 175 rewrites present in [XLA's algebraic simplifier](https://github.com/openxla/xla/blob/main/xla/hlo/transforms/simplifiers/algebraic_simplifier.cc) and is able to verify 115 of those in the unbounded setting.

## Publications

- [TensorRight: Automated Verification of Tensor Graph Rewrites](https://dl.acm.org/doi/10.1145/3704865) <br/>
Jai Arora, Sirui Lu, Devansh Jain, Tianfan Xu, Farzin Houshmand, Phitchaya Mangpo Phothilimthana, Mohsen Lesani, Praveen Narayanan, Karthik Srinivasa Murthy, Rastislav Bodik, Amit Sabne, and Charith Mendis. <br/>
In Proceedings of the 52nd ACM SIGPLAN Symposium on Principles of Programming Languages (POPL'25), January 2025, Denver, Colorado, USA

<details class="bibtex">
    <summary>BibTeX</summary>
    <pre><code>@article{10.1145/3704865,
author = {Arora, Jai and Lu, Sirui and Jain, Devansh and Xu, Tianfan and Houshmand, Farzin and Phothilimthana, Phitchaya Mangpo and Lesani, Mohsen and Narayanan, Praveen and Murthy, Karthik Srinivasa and Bodik, Rastislav and Sabne, Amit and Mendis, Charith},
title = {TensorRight: Automated Verification of Tensor Graph Rewrites},
year = {2025},
issue_date = {January 2025},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
volume = {9},
number = {POPL},
url = {https://doi.org/10.1145/3704865},
doi = {10.1145/3704865},
abstract = {Tensor compilers, essential for generating efficient code for deep learning models across various applications, employ tensor graph rewrites as one of the key optimizations. These rewrites optimize tensor computational graphs with the expectation of preserving semantics for tensors of arbitrary rank and size. Despite this expectation, to the best of our knowledge, there does not exist a fully automated verification system to prove the soundness of these rewrites for tensors of arbitrary rank and size. Previous works, while successful in verifying rewrites with tensors of concrete rank, do not provide guarantees in the unbounded setting.  To fill this gap, we introduce TensorRight, the first automatic verification system that can verify tensor graph rewrites for input tensors of arbitrary rank and size. We introduce a core language, TensorRight DSL, to represent rewrite rules using a novel axis definition, called aggregated-axis, which allows us to reason about an unbounded number of axes. We achieve unbounded verification by proving that there exists a bound on tensor ranks, under which bounded verification of all instances implies the correctness of the rewrite rule in the unbounded setting. We derive an algorithm to compute this rank using the denotational semantics of TensorRight DSL. TensorRight employs this algorithm to generate a finite number of bounded-verification proof obligations, which are then dispatched to an SMT solver using symbolic execution to automatically verify the correctness of the rewrite rules. We evaluate TensorRight’s verification capabilities by implementing rewrite rules present in XLA’s algebraic simplifier. The results demonstrate that TensorRight can prove the correctness of 115 out of 175 rules in their full generality, while the closest automatic, bounded-verification system can express only 18 of these rules.},
journal = {Proc. ACM Program. Lang.},
month = jan,
articleno = {29},
numpages = {32},
keywords = {Denotational Semantics, Tensor Compilers, Unbounded Verification}
}
</code></pre>
</details>

## Installation

### Installing Stack

`stack` and other tools in the Haskell Toolchain can be installed by following the instructions at [this link](https://www.haskell.org/ghcup/install/).

### Installing SMT Solvers

To verify the implemented rewrite rules, you need to install the Z3 and cvc5 SMT Solvers and make them available through `PATH`.

#### Installing Z3

On Ubuntu, you can install Z3 with:

```bash
apt update && apt install z3
```

On macOS, you can install Z3 with [Homebrew](https://brew.sh/):

```bash
brew install z3
```

Please refer to the [Z3 homepage](https://github.com/Z3Prover/z3) for more details.

#### Installing cvc5

cvc5 can be installed by downloading one of the pre-built binaries from [here](https://cvc5.github.io/downloads.html) or [building it from source](https://cvc5.github.io/docs/cvc5-1.2.0/installation/installation.html).

### Testing your Installation

You can test your installation by first cloning the repository, running regression tests and verifying rewrite rules.

#### Build

```bash
git clone https://github.com/ADAPT-uiuc/TensorRight.git && cd TensorRight/ && stack build

# Regression Tests: all testcases should pass
stack test

# Verifying Rewrite Rules: 115/118 passed
make verify
```

Running `make verify` tries to verify all the 118 implemented rewrite rules.
It results in 3 expected timeouts (the actual number could vary).

## Usage

We will now take a look at how we can use TensorRight DSL to express complex tensor graph rewrites with preconditions and verify them.
Please refer to the [implemented rules](./rules/) for more examples.

Consider the `DySliceToSlice` rule that we would like to express and verify in our DSL.

$$
\mathsf{dy\hbox{-}slice}(\mathsf{X}, B, L) \Rightarrow_{E - B' = L \ \wedge \ P = 1 \ \wedge \ B' = B } \mathsf{slice}(\mathsf{X}, B', E, P)
$$

The $\mathsf{dy\hbox{-}slice}$ operator extracts a sub-tensor from the input tensor $\mathsf{X}$, where the start-index for each axis is specified in $B$ and the length of the slice along each axis is passed in $L$. 
Meanwhile, the $\mathsf{slice}$ operator also extracts a sub-tensor from within a bounding box in the input tensor $\mathsf{X}$.
The start-indices for the bounding box are specified in $B'$, while the end-indices (exclusive) are specified in $E$.
$P$ specifies the stride for each axis, which determines the step size between elements in the bounding box.

The `DySliceToSlice` rule is generally not correct, unless $E - B'$ (the size of the bounding box in $\mathsf{slice}$) is equal to $L$ (the length in $\mathsf{dy\hbox{-}slice}$).
The other requirements are that $\mathsf{slice}$ should skip no elements, i.e., $P=1$, and the start indices in $\mathsf{slice}$ and $\mathsf{dy\hbox{-}slice}$ must be the same, i.e., $B' = B$.
Since these are specified in the precondition, the RHS expression is equivalent to the LHS expression.

We support verification of boolean, integer, and real valued tensors.
Since we would like to verify the `DySliceToSlice` rule for all tensor types, we declare the rule in our DSL as follows:

```haskell
rule :: forall a. AnyDTypeRule a
rule = do
  ...
```

We can use the type parameter `a` inside the rule definition to declare tensors of a polymorphic type.

We would like to verify the rule for an arbitrary number of named-axes in $\mathsf{X}$.
Since there is only one "role" of axes in the rewrite rule, i.e., every axis is getting sliced, we need only one aggregated-axis or one `RClass`, which we can declare using `newRClass`:

```haskell
rcls <- newRClass "rcls"
```

`rcls` can be thought of as an abstract set of named-axes, which can be instantiated to any number of named-axes.
This allows us to specify an abstract representation of a rewrite rule, which can be specialized to any rank.

We also want to verify the rule for arbitrary sizes and operator attributes like $B$, $E$, $L$, etc.
We represent these using abstract maps, which can be instantiated to maps of concrete rank.
We can declare maps on an `RClass` in our DSL using `newMaps`:

```haskell
[size, start, start', length, end, stride] <-
    newMaps ["size", "start", "start'", "length", "end", "stride"] rcls
```

We then declare an abstract tensor of shape `rcls --> size` containing elements of type `a` using `newTensor`:

```haskell
tensor <- newTensor @a "X" [rcls --> size]
```

The resulting tensor is said to have arbitrary values of type `a`.

We define LHS and RHS tensor expressions using the operators available in our DSL:

```haskell
lhs <-
  dynamicSlice tensor $
    DySlice {start = [rcls --> start], sizes = [rcls --> length]}
rhs <-
  slice tensor $
    Slice
    { start = [rcls --> start'],
      end = [rcls --> end],
      strides = [rcls --> stride]
    }
```

We can specify preconditions using `precondition`:

```haskell
precondition [end, start', length] $ \[e, s', l] -> e - s' .== l
precondition [stride] $ \[p] -> p .== 1
precondition [start, start'] $ \[s, s'] -> s' .== s
```

Finally, we declare a rewrite rule using the `rewrite` construct:

```haskell
rewrite "DynamicSlice(X) => Slice(X)" lhs rhs
```

Putting everything together, the specification of the `DySliceToSlice` rule in TensorRight DSL looks like the following:

```haskell
rule :: forall a. AnyDTypeRule a
rule = do
  rcls <- newRClass "rcls"
  [size, start, start', length, end, stride] <-
    newMaps ["size", "start", "start'", "length", "end", "stride"] rcls
  tensor <- newTensor @a "X" [rcls --> size]

  lhs <-
    dynamicSlice tensor $
      DySlice {start = [rcls --> start], sizes = [rcls --> length]}
  rhs <-
    slice tensor $
      Slice
      { start = [rcls --> start'],
        end = [rcls --> end],
        strides = [rcls --> stride]
      }

  precondition [end, start', length] $
    \[end, start', length] -> end - start' .== length
  precondition [stride] $ \[stride] -> stride .== 1
  precondition [start, start'] $ \[start, start'] -> start' .== start

  rewrite "DynamicSlice(X) => Slice(X)" lhs rhs
```

We can verify the rule by using `verifyAnyDTypeDSL`:

```haskell
main :: IO ()
main = do verifyAnyDTypeDSL rule
```

## Documentation

Please build the haddock doc using:
```bash
stack haddock
```

This will build the documentation in a folder like:

```bash
.stack-work/install/x86_64-linux/<hash>/9.8.2/doc/index.html
```

You can navigate to have a look at the full API documentation. If you are using
vscode, the live server plugin might be helpful for hosting the documentation.

### Code Formatting

We use [ormolu](https://hackage.haskell.org/package/ormolu) for formatting
Haskell source code.

## License
TensorRight is distributed under the terms of the Apache-2.0 license.
The [LICENSE](./LICENSE) file contains the full license text.
