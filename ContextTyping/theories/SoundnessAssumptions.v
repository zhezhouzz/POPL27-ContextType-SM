(** * ContextTyping.SoundnessAssumptions

    Artifact check file: compiling this file prints the assumptions of the
    top-level soundness theorems. *)

From ContextTyping Require Import Soundness.

Print Assumptions Fundamental.
Print Assumptions denotational_soundness.
Print Assumptions concrete_Fundamental.
Print Assumptions concrete_denotational_soundness.
