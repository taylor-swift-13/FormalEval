Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Fixpoint digitSum_fun (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String ch rest =>
      let code := nat_of_ascii ch in
      let is_upper := andb (Nat.leb 65 code) (Nat.leb code 90) in
      (if is_upper then code else 0) + digitSum_fun rest
  end.

Definition digitSum_spec (s : string) (sum : nat) : Prop :=
  sum = digitSum_fun s.

Example test_digitSum_complex: digitSum_spec 
  (append "VtabsBCDEFGHIJKLMNOPQRSTUVThis" 
    (String (ascii_of_nat 10) 
      (append "is" 
        (String (ascii_of_nat 9) 
          (append "a" 
            (String (ascii_of_nat 9) 
              (append "test" 
                (String (ascii_of_nat 9) 
                  (append "witestth" 
                    (String (ascii_of_nat 10) 
                      (append "newlines" 
                        (String (ascii_of_nat 9) 
                          (append "and" 
                            (String (ascii_of_nat 9) "tabsWXYAThisZ")
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  2269.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.