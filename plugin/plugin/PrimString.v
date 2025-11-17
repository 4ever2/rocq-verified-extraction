From Malfunction.Plugin Require Loader PrimInt63.
From Coq Require Import PrimString.

(* This only interfaces with primitive integers, so no particular wrapping is needed. *)
(* However the polymorphic functions HAVE TO be masked to remove type argument
  applications, hence typed erasure is required. *)

Verified Extract Constants [
  Coq.Strings.PrimString.string erased,
  Coq.Strings.PrimString.make => "Coq_verified_extraction_ocaml_ffi__Pstring.make",
  Coq.Strings.PrimString.length => "Coq_verified_extraction_ocaml_ffi__Pstring.length",
  Coq.Strings.PrimString.get => "Coq_verified_extraction_ocaml_ffi__Pstring.get",
  Coq.Strings.PrimString.sub => "Coq_verified_extraction_ocaml_ffi__Pstring.sub",
  Coq.Strings.PrimString.cat => "Coq_verified_extraction_ocaml_ffi__Pstring.cat",
  Coq.Strings.PrimString.compare => "Coq_verified_extraction_ocaml_ffi__Pstring.compare" ]
Packages [ "coq_verified_extraction_ocaml_ffi" ].
