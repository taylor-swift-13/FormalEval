Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition int := Z.

Inductive Any : Type :=
| AnyInt (i : int)
| AnyOther.

Definition IsInt (v : Any) (n : int) : Prop :=
  v = AnyInt n.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m H1 H2.
  rewrite H2 in H1.
  inversion H1.
  reflexivity.
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

Example test_filter_integers : filter_integers_spec [AnyInt 1; AnyInt (-1); AnyInt 0; AnyInt 999] [1; -1; 0; 999].
Proof.
  unfold filter_integers_spec.
  repeat (apply fir_cons_int; [ simpl; reflexivity | ]).
  apply fir_nil.
Qed.