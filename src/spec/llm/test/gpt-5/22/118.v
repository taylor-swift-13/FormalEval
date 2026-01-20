Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Inductive Any :=
| AInt : Z -> Any
| AList : list Any -> Any.

Definition int := Z.

Inductive IsInt : Any -> int -> Prop :=
| IsInt_mk : forall n, IsInt (AInt n) n.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
intros v n m Hn Hm.
destruct v as [k|l].
- inversion Hn; inversion Hm; subst; reflexivity.
- inversion Hn.
Qed.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Example test_case_new: filter_integers_spec
  [AInt 1%Z; AList []; AList []; AInt 8%Z; AList [AInt 5%Z]; AList [AInt 7%Z; AInt 8%Z]; AInt 9%Z; AInt 9%Z; AList []]
  [1%Z; 8%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [constructor|].
  eapply fir_cons_nonint; [intros n H; inversion H|].
  eapply fir_cons_nonint; [intros n H; inversion H|].
  eapply fir_cons_int; [constructor|].
  eapply fir_cons_nonint; [intros n H; inversion H|].
  eapply fir_cons_nonint; [intros n H; inversion H|].
  eapply fir_cons_int; [constructor|].
  eapply fir_cons_int; [constructor|].
  eapply fir_cons_nonint; [intros n H; inversion H|].
  constructor.
Qed.