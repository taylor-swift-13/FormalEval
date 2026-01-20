Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Parameter split_space : string -> list string -> Prop.
Parameter parse_int : string -> Z -> Prop.

Definition fruit_distribution_spec (s : string) (n : Z) (m : Z) : Prop :=
  exists tokens t0 t3 c1 c2,
    split_space s tokens /\
    nth_error tokens 0 = Some t0 /\
    nth_error tokens 3 = Some t3 /\
    parse_int t0 c1 /\
    parse_int t3 c2 /\
    0 <= n - c1 - c2 /\
    m = n - c1 - c2.