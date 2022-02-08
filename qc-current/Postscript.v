(** * Postscript *)

(* ################################################################# *)
(** * Future Directions *)

(** We have lots of plans for future directions:
       - Automatic derivation of generators and shrinkers for data
         satisfying Inductive relations
       - Vellum2 testing
       - DeepSpec Web Server
       - Testing-only variant of _Software Foundations_?
*)

(* ################################################################# *)
(** * Recommended Reading

    The material presented in this short course serves as an
    introduction to property based random testing using
    QuickChick. For the interested reader, we provide a few more
    references for additional reading:

    - The original QuickCheck paper by Koen Claessen and John Hughes
      from ICFP 2000.
      https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf

    - The original QuickChick paper that focuses on a framework for
      proving the correctness of QuickChick generators.
      https://hal.inria.fr/hal-01162898/document

    - A case study that uses QuickCheck to test non-interference for
      information-flow-control abstract machines.
      https://arxiv.org/abs/1409.0393v2

    - Code for that case study exists under the QuickChick
      organization of github (https://github.com/QuickChick) for
      both Haskell ("Testing Noninterference") and Coq ("IFC").

    - A paper on deriving QuickChick generators for a large class of
      inductive relations.
      https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf

    - Leo's PhD dissertation.
      https://lemonidas.github.io/pdf/Leo-PhD-Thesis.pdf
 *)

(* 2022-02-08 06:49:14 (UTC+00) *)
