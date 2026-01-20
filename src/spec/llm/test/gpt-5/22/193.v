Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameter v1 vlist23 v4 vlist5 vempty v1b vlist7_8 vobj vstr9 : Any.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v4 : IsInt v4 4%Z.
Axiom IsInt_v1b : IsInt v1b 1%Z.
Axiom NonInt_vlist23 : forall n, ~ IsInt vlist23 n.
Axiom NonInt_vlist5 : forall n, ~ IsInt vlist5 n.
Axiom NonInt_vempty : forall n, ~ IsInt vempty n.
Axiom NonInt_vlist7_8 : forall n, ~ IsInt vlist7_8 n.
Axiom NonInt_vobj : forall n, ~ IsInt vobj n.
Axiom NonInt_vstr9 : forall n, ~ IsInt vstr9 n.

Example test_case_mixed:
  filter_integers_spec
    [v1; vlist23; v4; vlist5; vempty; v1b; vlist7_8; vobj; vstr9]
    [1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact IsInt_v1.
  - eapply fir_cons_nonint.
    + intro n. apply NonInt_vlist23.
    + eapply fir_cons_int.
      * exact IsInt_v4.
      * eapply fir_cons_nonint.
        { intro n. apply NonInt_vlist5. }
        eapply fir_cons_nonint.
        { intro n. apply NonInt_vempty. }
        eapply fir_cons_int.
        { exact IsInt_v1b. }
        eapply fir_cons_nonint.
        { intro n. apply NonInt_vlist7_8. }
        eapply fir_cons_nonint.
        { intro n. apply NonInt_vobj. }
        eapply fir_cons_nonint.
        { intro n. apply NonInt_vstr9. }
        constructor.
Qed.