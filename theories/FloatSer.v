Fixpoint split_p (s : string) : option (string * string) :=
  match s with
  | String.EmptyString=> None
  | (c :: s) =>
      if eqb_byte "p" c then Some ("", s)
      else
      match split_p s with
      | None => None
      | Some (s1, s2) =>
        Some (c :: s1, s2)
      end
  end%bs.

Global
Instance Deserialize_spec_float : Deserialize SpecFloat.spec_float :=
  fun l e =>
    match e with
    | Atom_ (Str "-0.0") => inr (SpecFloat.S754_zero true)
    | Atom_ (Str "0.0") => inr (SpecFloat.S754_zero false)
    | Atom_ (Str "neg_infinity") => inr (SpecFloat.S754_infinity true)
    | Atom_ (Str "infinity") => inr (SpecFloat.S754_infinity false)
    | Atom_ (Str "nan") => inr SpecFloat.S754_nan
    | Atom_ (Str ("-" :: "0" :: "x" :: s)) =>
        match split_p s with
        | Some (p, z) =>
          let p := HexadecimalString.NilZero.uint_of_string (String.to_string p) in
          let z := DecimalString.NilZero.int_of_string (String.to_string z) in
          match p, z with
          | Some p, Some z =>
            let p := (Pos.of_hex_uint p) in
            let z := (Z.of_int z) in
            match p with
            | Npos p => inr (SpecFloat.S754_finite true p z)
            | _ => inl (DeserError l "could not read 'spec_float', expected hexadecimal string")
            end
          | _, _ => inl (DeserError l "could not read 'spec_float', expected hexadecimal string")
          end
        | None => inl (DeserError l "could not read 'spec_float', expected hexadecimal string")
        end
    | Atom_ (Str ("0" :: "x" :: s)) =>
        match split_p s with
        | Some (p, z) =>
          let p := HexadecimalString.NilZero.uint_of_string (String.to_string p) in
          let z := DecimalString.NilZero.int_of_string (String.to_string z) in
          match p, z with
          | Some p, Some z =>
            let p := (Pos.of_hex_uint p) in
            let z := (Z.of_int z) in
            match p with
            | Npos p => inr (SpecFloat.S754_finite false p z)
            | _ => inl (DeserError l "could not read 'spec_float', expected hexadecimal string")
            end
          | _, _ => inl (DeserError l "could not read 'spec_float', expected hexadecimal string")
          end
        | None => inl (DeserError l "could not read 'spec_float', expected hexadecimal string")
        end
    | Atom_ (Str (_ :: _ :: _)) =>  inl (DeserError l "could not read 'spec_float', expected hexadecimal string")
    | Atom_ _ => inl (DeserError l "could not read 'spec_float', got non-string atom")
    | List _ => inl (DeserError l "could not read 'spec_float', got list")
    end%bs.

Global
Instance Serialize_spec_float : Serialize SpecFloat.spec_float :=
  fun f =>
    let s :=
      match f with
      | SpecFloat.S754_zero sign =>
          if sign then "-0.0" else "0.0"
      | SpecFloat.S754_infinity sign =>
          if sign then "neg_infinity" else "infinity"
      | SpecFloat.S754_nan =>
          "nan"
      | SpecFloat.S754_finite sign p z =>
          let abs :=
          "0x" ++ String.of_string (HexadecimalString.NilZero.string_of_uint (N.to_hex_uint (Npos p))) ++ "p" ++
            String.of_string (DecimalString.NilZero.string_of_int (Z.to_int z))
          in
          if sign then "-" ++ abs else abs
      end%bs in
    Atom (Str s).










Local Fixpoint contains (b : byte) (s : string) : bool :=
  match s with
  | "" => false
  | (c :: s) =>
    if eqb_byte b c then true
    else contains b s
  end%bs.

Local Lemma contains_cons_neq : forall b1 b2 s,
  contains b1 (b2 :: s)%bs = false ->
    eqb_byte b1 b2 = false.
Proof.
  intros.
  cbn in H.
  destruct eqb_byte; auto.
Qed.
Local Lemma contains_cons : forall b1 b2 s,
  contains b1 (b2 :: s)%bs = false ->
    contains b1 s = false.
Proof.
  intros.
  cbn in H.
  destruct eqb_byte.
  - discriminate.
  - exact H.
Qed.

Local Lemma split_p_eq : forall s1 s2,
  contains "p" s1 = false ->
  split_p (s1 ++ "p" :: s2)%bs = Some (s1, s2).
Proof.
  intros.
  induction s1.
  - cbn. reflexivity.
  - cbn.
    erewrite contains_cons_neq; eauto.
    apply contains_cons in H.
    apply IHs1 in H.
    rewrite H.
    reflexivity.
Qed.

Local Lemma split_p_eq_some : forall s s1 s2,
  split_p s = Some (s1, s2) ->
    s = (s1 ++ "p" :: s2)%bs.
Proof.
  induction s.
  - cbn in *. discriminate.
  - intros.
    cbn in H.
    destruct eqb_byte eqn:Hb in H.
    + inversion_clear H.
      unfold eqb_byte in Hb.
      rewrite ByteCompareSpec.eqb_compare in Hb.
      destruct ByteCompare.compare eqn:Hb'; try discriminate.
      apply ByteCompareSpec.compare_eq in Hb' as <-.
      reflexivity.
    + destruct split_p eqn:Hsplit in H; try discriminate.
      destruct p eqn:Hp. inversion H; subst; clear H.
      apply IHs in Hsplit as ->.
      cbn.
      reflexivity.
Qed.

From Stdlib Require DecimalZ DecimalPos HexadecimalPos.

Local Lemma z_to_int_nonnil : forall n,
  Z.to_int n <> Decimal.Pos Decimal.Nil.
Proof.
  intros.
  destruct n; try easy.
  cbn.
  intros H.
  inversion H.
  apply DecimalPos.Unsigned.to_uint_nonnil in H1.
  assumption.
Qed.

Local Lemma z_to_int_nonnil' : forall n,
  Z.to_int n <> Decimal.Neg Decimal.Nil.
Proof.
  intros.
  destruct n; try easy.
  cbn.
  intros H.
  inversion H.
  apply DecimalPos.Unsigned.to_uint_nonnil in H1.
  assumption.
Qed.

Local Lemma no_p_string_of_uint' : forall n,
  contains "p"
    (String.of_string
      (HexadecimalString.NilEmpty.string_of_uint n)) = false.
Proof.
  induction n; cbn; try reflexivity.
  all: rewrite neqb_byte_neq; [apply IHn | easy].
Qed.

Local Lemma no_p_string_of_uint : forall n,
  contains "p"
    (String.of_string
      (HexadecimalString.NilZero.string_of_uint n)) = false.
Proof.
  intros.
  destruct n; try reflexivity; cbn.
  all: rewrite neqb_byte_neq; [apply no_p_string_of_uint' | easy].
Qed.

Global
Instance CompleteClass_spec_float : CompleteClass SpecFloat.spec_float.
Proof.
  unfold CompleteClass, Complete.
  intros l [].
  - destruct s.
    reflexivity.
    reflexivity.
  - destruct s.
    reflexivity.
    reflexivity.
  - reflexivity.
  - destruct s.
    + cbn.
      rewrite split_p_eq.
      rewrite 2!bytestring_complete.
      rewrite HexadecimalString.NilZero.usu.
      rewrite DecimalString.NilZero.isi.
      rewrite HexadecimalPos.Unsigned.of_to.
      rewrite DecimalZ.of_to.
      reflexivity.
      apply z_to_int_nonnil.
      apply z_to_int_nonnil'.
      apply HexadecimalPos.Unsigned.to_uint_nonnil.
      apply no_p_string_of_uint.
    + cbn.
      rewrite split_p_eq.
      rewrite 2!bytestring_complete.
      rewrite HexadecimalString.NilZero.usu.
      rewrite DecimalString.NilZero.isi.
      rewrite HexadecimalPos.Unsigned.of_to.
      rewrite DecimalZ.of_to.
      reflexivity.
      apply z_to_int_nonnil.
      apply z_to_int_nonnil'.
      apply HexadecimalPos.Unsigned.to_uint_nonnil.
      apply no_p_string_of_uint.
Qed.

Local Ltac destruct_match H :=
  match type of H with
  | (match ?expr with _ => _ end = inr _) =>
      destruct expr; try discriminate
  end.

(* Local Lemma q : forall n p,
  Pos.of_hex_uint n = N.pos p ->
    Pos.to_hex_uint p = n.
Proof.
  intros.
  N.to_hex_uint
  specialize HexadecimalPos.Unsigned.to_uint_pos_surj as H0.
  edestruct H0. *)

Global
Instance SoundClass_spec_float : SoundClass SpecFloat.spec_float.
Proof.
  intros l e a Ee.
  unfold _from_sexp, Deserialize_spec_float in Ee.
  destruct_match Ee.
  destruct_match Ee.
  destruct_match Ee.
  destruct_match Ee; destruct_match Ee.
  - (* -0.0 or -n *)
    do 3 destruct_match Ee.
    + (* -0.0 *)
      do 3 destruct_match Ee.
      injection Ee as <-.
      reflexivity.
    + (* -n *)
      destruct split_p eqn:Hsplit; try discriminate.
      destruct p; eapply split_p_eq_some in Hsplit.
      destruct HexadecimalString.NilZero.uint_of_string eqn:Hp; try discriminate.
      apply HexadecimalString.NilZero.sus in Hp.
      destruct DecimalString.NilZero.int_of_string eqn:Hz; try discriminate.
      apply DecimalString.NilZero.sis in Hz.
      destruct Pos.of_hex_uint eqn:Hu; try discriminate.

      injection Ee as <-.
      unfold to_sexp, Serialize_spec_float.
      rewrite <- Hu.
      rewrite HexadecimalPos.Unsigned.to_of.
      rewrite DecimalZ.to_of.

      Search (Hexadecimal.unorm).

      assert (H: (Hexadecimal.unorm u) = u) by admit;
        rewrite H; clear H.
      assert (H: (Decimal.norm s0) = s0) by admit;
        rewrite H; clear H.
      rewrite Hp, Hz.
      rewrite 2? bytestring_sound.
      rewrite Hsplit; cbn.
      reflexivity.
  - (* 0.0 or n *)
    do 1 destruct_match Ee.
    + (* 0.0 *)
      do 3 destruct_match Ee.
      injection Ee as <-.
      reflexivity.
    + (* n *)
      destruct split_p eqn:Hsplit; try discriminate.
      destruct p; eapply split_p_eq_some in Hsplit.
      destruct HexadecimalString.NilZero.uint_of_string eqn:Hp; try discriminate.
      apply HexadecimalString.NilZero.sus in Hp.
      destruct DecimalString.NilZero.int_of_string eqn:Hz; try discriminate.
      apply DecimalString.NilZero.sis in Hz.
      destruct Pos.of_hex_uint eqn:Hu; try discriminate.

      injection Ee as <-.
      unfold to_sexp, Serialize_spec_float.
      rewrite <- Hu.
      rewrite HexadecimalPos.Unsigned.to_of.
      rewrite DecimalZ.to_of.
      assert (H: (Hexadecimal.unorm u) = u) by admit;
        rewrite H; clear H.
      assert (H: (Decimal.norm s0) = s0) by admit;
        rewrite H; clear H.
      rewrite Hp, Hz.
      rewrite 2? bytestring_sound.
      rewrite Hsplit; cbn.
      reflexivity.
  - (* infinity *)
    do 14 destruct_match Ee.
    injection Ee as <-.
    reflexivity.
  - (* nan or -infinity *)
    do 1 destruct_match Ee.
    + (* nan *)
      do 3 destruct_match Ee.
      injection Ee as <-.
      reflexivity.
    + (* - infinity *)
      do 21 destruct_match Ee.
      injection Ee as <-.
      reflexivity.
Admitted.
