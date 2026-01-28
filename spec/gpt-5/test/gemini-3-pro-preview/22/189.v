Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition int := Z.

Inductive Any : Type :=
| AnyInt (v : int)
| AnyList (l : list Any).

Inductive IsInt : Any -> int -> Prop :=
| IsInt_intro : forall n, IsInt (AnyInt n) n.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m H1 H2.
  inversion H1; subst.
  inversion H2; subst.
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

Example test_filter_integers : 
  filter_integers_spec 
    [AnyInt 1; AnyList []; AnyList []; AnyInt 8; AnyList [AnyInt 5]; 
     AnyList [AnyInt 8; AnyInt 7; AnyInt 8]; AnyList [AnyInt 8; AnyInt 7; AnyInt 8]; 
     AnyInt 9; AnyInt 9; AnyList []] 
    [1; 8; 9; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n:=1). apply IsInt_intro.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_int with (n:=8). apply IsInt_intro.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_int with (n:=9). apply IsInt_intro.
  apply fir_cons_int with (n:=9). apply IsInt_intro.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_nil.
Qed.