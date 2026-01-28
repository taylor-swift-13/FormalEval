Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Open Scope string_scope.
Open Scope Z_scope.

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

Parameter z2i : Z -> int.
Parameter AnyInt : Z -> Any.
Parameter AnyBool : bool -> Any.
Parameter AnyNone : Any.
Parameter AnyString : string -> Any.
Parameter AnyList : list Any -> Any.
Parameter AnyFloat : R -> Any.
Parameter real_3_14 : R.

Axiom IsInt_AnyInt : forall z, IsInt (AnyInt z) (z2i z).
Axiom Not_IsInt_AnyBool : forall b n, ~ IsInt (AnyBool b) n.
Axiom Not_IsInt_AnyNone : forall n, ~ IsInt AnyNone n.
Axiom Not_IsInt_AnyString : forall s n, ~ IsInt (AnyString s) n.
Axiom Not_IsInt_AnyList : forall l n, ~ IsInt (AnyList l) n.
Axiom Not_IsInt_AnyFloat : forall r n, ~ IsInt (AnyFloat r) n.

Example test_filter_integers : 
  filter_integers_spec 
    [AnyBool true; AnyBool false; AnyNone; AnyInt 0; AnyInt (-10); 
     AnyString "test"; AnyList [AnyInt 8]; AnyList []; AnyFloat real_3_14; AnyNone] 
    [z2i 0; z2i (-10)].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint; [apply Not_IsInt_AnyBool |].
  apply fir_cons_nonint; [apply Not_IsInt_AnyBool |].
  apply fir_cons_nonint; [apply Not_IsInt_AnyNone |].
  apply fir_cons_int with (n := z2i 0); [apply IsInt_AnyInt |].
  apply fir_cons_int with (n := z2i (-10)); [apply IsInt_AnyInt |].
  apply fir_cons_nonint; [apply Not_IsInt_AnyString |].
  apply fir_cons_nonint; [apply Not_IsInt_AnyList |].
  apply fir_cons_nonint; [apply Not_IsInt_AnyList |].
  apply fir_cons_nonint; [apply Not_IsInt_AnyFloat |].
  apply fir_cons_nonint; [apply Not_IsInt_AnyNone |].
  apply fir_nil.
Qed.