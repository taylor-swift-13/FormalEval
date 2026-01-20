Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Any.

Axiom a1_is : IsInt a1 1%Z.
Axiom a3_is : IsInt a3 4%Z.
Axiom a10_is : IsInt a10 1%Z.

Axiom a2_not : forall n, ~ IsInt a2 n.
Axiom a4_not : forall n, ~ IsInt a4 n.
Axiom a5_not : forall n, ~ IsInt a5 n.
Axiom a6_not : forall n, ~ IsInt a6 n.
Axiom a7_not : forall n, ~ IsInt a7 n.
Axiom a8_not : forall n, ~ IsInt a8 n.
Axiom a9_not : forall n, ~ IsInt a9 n.

Example test_case: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] [1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact a1_is |].
  eapply fir_cons_nonint; [exact a2_not |].
  eapply fir_cons_int; [exact a3_is |].
  eapply fir_cons_nonint; [exact a4_not |].
  eapply fir_cons_nonint; [exact a5_not |].
  eapply fir_cons_nonint; [exact a6_not |].
  eapply fir_cons_nonint; [exact a7_not |].
  eapply fir_cons_nonint; [exact a8_not |].
  eapply fir_cons_nonint; [exact a9_not |].
  eapply fir_cons_int; [exact a10_is |].
  constructor.
Qed.