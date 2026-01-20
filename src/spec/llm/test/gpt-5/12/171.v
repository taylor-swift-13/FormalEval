Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition longest_spec (strings : list string) (res : option string) : Prop :=
  match strings with
  | [] => res = None
  | _ =>
    exists l1 s l2,
      strings = l1 ++ s :: l2 /\
      res = Some s /\
      (forall t, In t strings -> String.length t <= String.length s) /\
      (forall t, In t l1 -> String.length t < String.length s)
  end.

Example test_longest_spec_case :
  longest_spec
    ["abc"%string; "defghijklAvocadomnop"%string; "eeeeeeeeee"%string; "Orange"%string; ""%string; "qr"%string]
    (Some "defghijklAvocadomnop"%string).
Proof.
  unfold longest_spec; simpl.
  exists ["abc"%string].
  exists "defghijklAvocadomnop"%string.
  exists ["eeeeeeeeee"%string; "Orange"%string; ""%string; "qr"%string].
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * intros t Hin.
        simpl in Hin.
        destruct Hin as [H|Hin1]; subst; cbn; try lia.
        destruct Hin1 as [H|Hin2]; subst; cbn; try lia.
        destruct Hin2 as [H|Hin3]; subst; cbn; try lia.
        destruct Hin3 as [H|Hin4]; subst; cbn; try lia.
        destruct Hin4 as [H|Hin5]; subst; cbn; try lia.
        destruct Hin5 as [H|[]]; subst; cbn; lia.
      * intros t Hin.
        simpl in Hin.
        destruct Hin as [H|[]]; subst; cbn; lia.
Qed.