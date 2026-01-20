Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

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

Parameter a1 a10 a9 b c : Any.
Parameter i1 i10 i9 : int.
Notation "1%Z" := i1.
Notation "10%Z" := i10.
Notation "9%Z" := i9.
Axiom IsInt_a1 : IsInt a1 1%Z.
Axiom IsInt_a10 : IsInt a10 10%Z.
Axiom IsInt_a9 : IsInt a9 9%Z.
Axiom b_nonint : forall n, ~ IsInt b n.
Axiom c_nonint : forall n, ~ IsInt c n.

Example test_case_mixed: filter_integers_spec [a1; b; a10; a9; c] [1%Z; 10%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a1|].
  eapply fir_cons_nonint; [apply b_nonint|].
  eapply fir_cons_int; [apply IsInt_a10|].
  eapply fir_cons_int; [apply IsInt_a9|].
  eapply fir_cons_nonint; [apply c_nonint|].
  constructor.
Qed.