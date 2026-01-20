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

Parameter a1 a2 a3 a4 a5 : Any.
Axiom a1_is_int : IsInt a1 1%Z.
Axiom a2_not_int : forall n, ~ IsInt a2 n.
Axiom a3_not_int : forall n, ~ IsInt a3 n.
Axiom a4_is_int : IsInt a4 8%Z.
Axiom a5_is_int : IsInt a5 1%Z.

Example test_case_mixed: filter_integers_spec [a1; a2; a3; a4; a5] [1%Z; 8%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact a1_is_int |].
  eapply fir_cons_nonint; [exact a2_not_int |].
  eapply fir_cons_nonint; [exact a3_not_int |].
  eapply fir_cons_int; [exact a4_is_int |].
  eapply fir_cons_int; [exact a5_is_int |].
  constructor.
Qed.