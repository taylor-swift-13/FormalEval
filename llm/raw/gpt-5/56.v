
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Fixpoint good_from (acc : Z) (s : string) : Prop :=
  match s with
  | EmptyString => acc = 0%Z
  | String c rest =>
      let acc' :=
        acc +
        (if Ascii.eqb c (ascii_of_nat 60) then 1%Z
         else if Ascii.eqb c (ascii_of_nat 62) then (-1)%Z
         else 0%Z) in
      (0 <= acc')%Z /\ good_from acc' rest
  end.

Definition correct_bracketing_prop (s : string) : Prop :=
  good_from 0%Z s.

Definition correct_bracketing_spec (brackets : string) (res : bool) : Prop :=
  if res then correct_bracketing_prop brackets else ~ correct_bracketing_prop brackets.
