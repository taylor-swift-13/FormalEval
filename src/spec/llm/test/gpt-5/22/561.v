Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

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

Parameter v_neg46 v_2 v_1 v_one v_sixmap : Any.
Axiom IsInt_neg46 : IsInt v_neg46 (-46%Z).
Axiom IsInt_2 : IsInt v_2 (2%Z).
Axiom IsInt_1 : IsInt v_1 (1%Z).
Axiom NonInt_one : forall n, ~ IsInt v_one n.
Axiom NonInt_sixmap : forall n, ~ IsInt v_sixmap n.

Example test_case_mixed: filter_integers_spec [v_neg46; v_2; v_1; v_one; v_sixmap] [-46%Z; 2%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_neg46 |].
  eapply fir_cons_int; [apply IsInt_2 |].
  eapply fir_cons_int; [apply IsInt_1 |].
  eapply fir_cons_nonint; [apply NonInt_one |].
  eapply fir_cons_nonint; [apply NonInt_sixmap |].
  apply fir_nil.
Qed.