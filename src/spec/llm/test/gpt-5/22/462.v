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

Parameter empty1 empty2 list6 listbools listints list78 list6b item9 list6c list6d list6e empty3 : Any.
Axiom nonint_empty1 : forall n, ~ IsInt empty1 n.
Axiom nonint_empty2 : forall n, ~ IsInt empty2 n.
Axiom nonint_list6 : forall n, ~ IsInt list6 n.
Axiom nonint_listbools : forall n, ~ IsInt listbools n.
Axiom nonint_listints : forall n, ~ IsInt listints n.
Axiom nonint_list78 : forall n, ~ IsInt list78 n.
Axiom nonint_list6b : forall n, ~ IsInt list6b n.
Axiom is_item9 : IsInt item9 9%Z.
Axiom nonint_list6c : forall n, ~ IsInt list6c n.
Axiom nonint_list6d : forall n, ~ IsInt list6d n.
Axiom nonint_list6e : forall n, ~ IsInt list6e n.
Axiom nonint_empty3 : forall n, ~ IsInt empty3 n.

Example test_case_nested:
  filter_integers_spec
    [empty1; empty2; list6; listbools; listints; list78; list6b; item9; list6c; list6d; list6e; empty3]
    [9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact nonint_empty1.
  eapply fir_cons_nonint. exact nonint_empty2.
  eapply fir_cons_nonint. exact nonint_list6.
  eapply fir_cons_nonint. exact nonint_listbools.
  eapply fir_cons_nonint. exact nonint_listints.
  eapply fir_cons_nonint. exact nonint_list78.
  eapply fir_cons_nonint. exact nonint_list6b.
  eapply fir_cons_int.
  - exact is_item9.
  - eapply fir_cons_nonint. exact nonint_list6c.
    eapply fir_cons_nonint. exact nonint_list6d.
    eapply fir_cons_nonint. exact nonint_list6e.
    eapply fir_cons_nonint. exact nonint_empty3.
    constructor.
Qed.