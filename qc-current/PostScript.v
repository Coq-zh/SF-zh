(** * PostScript *)

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
(** * Recommended Reading *)
(** The material presented in this short course serves as an
    introduction to property based random testing using
    QuickChick. For the interested reader, we provide a few more
    references for additional reading:

    - The original QuickCheck paper by Koen Claessen and John Hughes
      from ICFP 2000. 
      http://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf

    - The original QuickChick paper that focuses on a framework for
      proving the correctness of QuickChick generators.
      http://www.cis.upenn.edu/~llamp/pdf/Foundational.pdf

    - A case study that uses QuickCheck to test non-interference for
      information-flow-control abstract machines.
      http://www.cis.upenn.edu/~llamp/pdf/TestingNonInterferenceQuickly.pdf

    - Code for that case study exists under the QuickChick
      organization of github (https://github.com/QuickChick) for
      both Haskell ("Testing Noninterference") and Coq ("IFC").

    - A paper on deriving QuickChick generators for a large class of
      inductive relations. 
      http://www.cis.upenn.edu/~llamp/pdf/GeneratingGoodGenerators.pdf

    - Leo's PhD dissertation.
      https://lemonidas.github.io/pdf/Leo-PhD-Thesis.pdf
 *)
