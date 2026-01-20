Require Import Coq.Init.Logic.

Definition string_sequence_spec (n : int) (s : str) : Prop :=
s = join " " (map str (range (n + 1))).