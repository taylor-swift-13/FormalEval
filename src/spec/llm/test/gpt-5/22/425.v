Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int : Type := Z.
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

Parameter a2 a1 a_one1 a_list123 a_dict_six6_1 a5 a_dict_six6_2 a_one2 : Any.
Axiom IsInt_a2 : IsInt a2 (2%Z).
Axiom IsInt_a1 : IsInt a1 (1%Z).
Axiom IsInt_a5 : IsInt a5 (5%Z).
Axiom NonInt_a_one1 : forall n, ~ IsInt a_one1 n.
Axiom NonInt_a_list123 : forall n, ~ IsInt a_list123 n.
Axiom NonInt_a_dict_six6_1 : forall n, ~ IsInt a_dict_six6_1 n.
Axiom NonInt_a_dict_six6_2 : forall n, ~ IsInt a_dict_six6_2 n.
Axiom NonInt_a_one2 : forall n, ~ IsInt a_one2 n.

Example test_case_mixed: filter_integers_spec [a2; a1; a_one1; a_list123; a_dict_six6_1; a5; a_dict_six6_2; a_one2] [2%Z; 1%Z; 5%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_a2 |].
  eapply fir_cons_int; [exact IsInt_a1 |].
  eapply fir_cons_nonint; [exact NonInt_a_one1 |].
  eapply fir_cons_nonint; [exact NonInt_a_list123 |].
  eapply fir_cons_nonint; [exact NonInt_a_dict_six6_1 |].
  eapply fir_cons_int; [exact IsInt_a5 |].
  eapply fir_cons_nonint; [exact NonInt_a_dict_six6_2 |].
  eapply fir_cons_nonint; [exact NonInt_a_one2 |].
  constructor.
Qed.