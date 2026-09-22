From Coq Require Import List String ZArith.
From compcert Require Import AST Maps Integers Floats Asm.
From CminorImport Require Import ExportCminor.

Import ListNotations ExportCminor.
Local Open Scope string_scope.

(** Generated from every constructor of the pinned x86/Asm.v. *)

Definition ireg (r : Asm.ireg) : string :=
  match r with
  | RAX => "RAX"
  | RBX => "RBX"
  | RCX => "RCX"
  | RDX => "RDX"
  | RSI => "RSI"
  | RDI => "RDI"
  | RBP => "RBP"
  | RSP => "RSP"
  | R8 => "R8"
  | R9 => "R9"
  | R10 => "R10"
  | R11 => "R11"
  | R12 => "R12"
  | R13 => "R13"
  | R14 => "R14"
  | R15 => "R15"
  end.

Definition freg (r : Asm.freg) : string :=
  match r with
  | XMM0 => "XMM0"
  | XMM1 => "XMM1"
  | XMM2 => "XMM2"
  | XMM3 => "XMM3"
  | XMM4 => "XMM4"
  | XMM5 => "XMM5"
  | XMM6 => "XMM6"
  | XMM7 => "XMM7"
  | XMM8 => "XMM8"
  | XMM9 => "XMM9"
  | XMM10 => "XMM10"
  | XMM11 => "XMM11"
  | XMM12 => "XMM12"
  | XMM13 => "XMM13"
  | XMM14 => "XMM14"
  | XMM15 => "XMM15"
  end.

Definition crbit (r : Asm.crbit) : string :=
  match r with
  | ZF => "ZF"
  | CF => "CF"
  | PF => "PF"
  | SF => "SF"
  | OF => "OF"
  end.

Definition condition (r : Asm.testcond) : string :=
  match r with
  | Cond_e => "Cond_e"
  | Cond_ne => "Cond_ne"
  | Cond_b => "Cond_b"
  | Cond_be => "Cond_be"
  | Cond_ae => "Cond_ae"
  | Cond_a => "Cond_a"
  | Cond_l => "Cond_l"
  | Cond_le => "Cond_le"
  | Cond_ge => "Cond_ge"
  | Cond_g => "Cond_g"
  | Cond_p => "Cond_p"
  | Cond_np => "Cond_np"
  end.

Definition preg (r : Asm.preg) : string :=
  match r with
  | PC => "PC" | IR r => node "IR" [ireg r]
  | FR r => node "FR" [freg r] | ST0 => "ST0"
  | CR b => node "CR" [crbit b] | RA => "RA"
  end.

Definition optional {A} (render : A -> string) (value : option A) : string :=
  match value with None => "none" | Some x => node "some" [render x] end.

Definition index (p : Asm.ireg * Z) : string :=
  node "pair" [ireg (fst p); number (snd p)].

Definition displacement (d : Z + ident * ptrofs) : string :=
  match d with
  | inl z => node "inl" [number z]
  | inr p => node "inr" [node "pair" [identifier (fst p); offset (snd p)]]
  end.

Definition address (a : Asm.addrmode) : string :=
  match a with
  | Addrmode base ofs const =>
      node "Addrmode" [optional ireg base; optional index ofs; displacement const]
  end.

Fixpoint builtinarg (a : builtin_arg Asm.preg) : string :=
  match a with
  | BA r => node "BA" [preg r]
  | BA_int n => node "BA_int" [int n]
  | BA_long n => node "BA_long" [long n]
  | BA_float f => node "BA_float" [float f]
  | BA_single f => node "BA_single" [single f]
  | BA_loadstack c ofs => node "BA_loadstack" [chunk c; offset ofs]
  | BA_addrstack ofs => node "BA_addrstack" [offset ofs]
  | BA_loadglobal c id ofs => node "BA_loadglobal" [chunk c; identifier id; offset ofs]
  | BA_addrglobal id ofs => node "BA_addrglobal" [identifier id; offset ofs]
  | BA_splitlong hi lo => node "BA_splitlong" [builtinarg hi; builtinarg lo]
  | BA_addptr a b => node "BA_addptr" [builtinarg a; builtinarg b]
  end.

Fixpoint builtinres (r : builtin_res Asm.preg) : string :=
  match r with
  | BR r => node "BR" [preg r]
  | BR_none => "BR_none"
  | BR_splitlong hi lo => node "BR_splitlong" [builtinres hi; builtinres lo]
  end.

Definition instruction (i : Asm.instruction) : string :=
  match i with
  | Pmov_rr rd r1 => node "Pmov_rr" [ireg rd; ireg r1]
  | Pmovl_ri rd n => node "Pmovl_ri" [ireg rd; int n]
  | Pmovq_ri rd n => node "Pmovq_ri" [ireg rd; long n]
  | Pmov_rs rd id => node "Pmov_rs" [ireg rd; identifier id]
  | Pmovl_rm rd a => node "Pmovl_rm" [ireg rd; address a]
  | Pmovq_rm rd a => node "Pmovq_rm" [ireg rd; address a]
  | Pmovl_mr a rs => node "Pmovl_mr" [address a; ireg rs]
  | Pmovq_mr a rs => node "Pmovq_mr" [address a; ireg rs]
  | Pmovsd_ff rd r1 => node "Pmovsd_ff" [freg rd; freg r1]
  | Pmovsd_fi rd n => node "Pmovsd_fi" [freg rd; float n]
  | Pmovsd_fm rd a => node "Pmovsd_fm" [freg rd; address a]
  | Pmovsd_mf a r1 => node "Pmovsd_mf" [address a; freg r1]
  | Pmovss_fi rd n => node "Pmovss_fi" [freg rd; single n]
  | Pmovss_fm rd a => node "Pmovss_fm" [freg rd; address a]
  | Pmovss_mf a r1 => node "Pmovss_mf" [address a; freg r1]
  | Pfldl_m a => node "Pfldl_m" [address a]
  | Pfstpl_m a => node "Pfstpl_m" [address a]
  | Pflds_m a => node "Pflds_m" [address a]
  | Pfstps_m a => node "Pfstps_m" [address a]
  | Pmovb_mr a rs => node "Pmovb_mr" [address a; ireg rs]
  | Pmovw_mr a rs => node "Pmovw_mr" [address a; ireg rs]
  | Pmovzb_rr rd rs => node "Pmovzb_rr" [ireg rd; ireg rs]
  | Pmovzb_rm rd a => node "Pmovzb_rm" [ireg rd; address a]
  | Pmovsb_rr rd rs => node "Pmovsb_rr" [ireg rd; ireg rs]
  | Pmovsb_rm rd a => node "Pmovsb_rm" [ireg rd; address a]
  | Pmovzw_rr rd rs => node "Pmovzw_rr" [ireg rd; ireg rs]
  | Pmovzw_rm rd a => node "Pmovzw_rm" [ireg rd; address a]
  | Pmovsw_rr rd rs => node "Pmovsw_rr" [ireg rd; ireg rs]
  | Pmovsw_rm rd a => node "Pmovsw_rm" [ireg rd; address a]
  | Pmovzl_rr rd rs => node "Pmovzl_rr" [ireg rd; ireg rs]
  | Pmovsl_rr rd rs => node "Pmovsl_rr" [ireg rd; ireg rs]
  | Pmovls_rr rd => node "Pmovls_rr" [ireg rd]
  | Pcvtsd2ss_ff rd r1 => node "Pcvtsd2ss_ff" [freg rd; freg r1]
  | Pcvtss2sd_ff rd r1 => node "Pcvtss2sd_ff" [freg rd; freg r1]
  | Pcvttsd2si_rf rd r1 => node "Pcvttsd2si_rf" [ireg rd; freg r1]
  | Pcvtsi2sd_fr rd r1 => node "Pcvtsi2sd_fr" [freg rd; ireg r1]
  | Pcvttss2si_rf rd r1 => node "Pcvttss2si_rf" [ireg rd; freg r1]
  | Pcvtsi2ss_fr rd r1 => node "Pcvtsi2ss_fr" [freg rd; ireg r1]
  | Pcvttsd2sl_rf rd r1 => node "Pcvttsd2sl_rf" [ireg rd; freg r1]
  | Pcvtsl2sd_fr rd r1 => node "Pcvtsl2sd_fr" [freg rd; ireg r1]
  | Pcvttss2sl_rf rd r1 => node "Pcvttss2sl_rf" [ireg rd; freg r1]
  | Pcvtsl2ss_fr rd r1 => node "Pcvtsl2ss_fr" [freg rd; ireg r1]
  | Pleal rd a => node "Pleal" [ireg rd; address a]
  | Pleaq rd a => node "Pleaq" [ireg rd; address a]
  | Pnegl rd => node "Pnegl" [ireg rd]
  | Pnegq rd => node "Pnegq" [ireg rd]
  | Paddl_ri rd n => node "Paddl_ri" [ireg rd; int n]
  | Paddq_ri rd n => node "Paddq_ri" [ireg rd; long n]
  | Psubl_rr rd r1 => node "Psubl_rr" [ireg rd; ireg r1]
  | Psubq_rr rd r1 => node "Psubq_rr" [ireg rd; ireg r1]
  | Pimull_rr rd r1 => node "Pimull_rr" [ireg rd; ireg r1]
  | Pimulq_rr rd r1 => node "Pimulq_rr" [ireg rd; ireg r1]
  | Pimull_ri rd n => node "Pimull_ri" [ireg rd; int n]
  | Pimulq_ri rd n => node "Pimulq_ri" [ireg rd; long n]
  | Pimull_r r1 => node "Pimull_r" [ireg r1]
  | Pimulq_r r1 => node "Pimulq_r" [ireg r1]
  | Pmull_r r1 => node "Pmull_r" [ireg r1]
  | Pmulq_r r1 => node "Pmulq_r" [ireg r1]
  | Pcltd => "Pcltd"
  | Pcqto => "Pcqto"
  | Pdivl r1 => node "Pdivl" [ireg r1]
  | Pdivq r1 => node "Pdivq" [ireg r1]
  | Pidivl r1 => node "Pidivl" [ireg r1]
  | Pidivq r1 => node "Pidivq" [ireg r1]
  | Pandl_rr rd r1 => node "Pandl_rr" [ireg rd; ireg r1]
  | Pandq_rr rd r1 => node "Pandq_rr" [ireg rd; ireg r1]
  | Pandl_ri rd n => node "Pandl_ri" [ireg rd; int n]
  | Pandq_ri rd n => node "Pandq_ri" [ireg rd; long n]
  | Porl_rr rd r1 => node "Porl_rr" [ireg rd; ireg r1]
  | Porq_rr rd r1 => node "Porq_rr" [ireg rd; ireg r1]
  | Porl_ri rd n => node "Porl_ri" [ireg rd; int n]
  | Porq_ri rd n => node "Porq_ri" [ireg rd; long n]
  | Pxorl_r rd => node "Pxorl_r" [ireg rd]
  | Pxorq_r rd => node "Pxorq_r" [ireg rd]
  | Pxorl_rr rd r1 => node "Pxorl_rr" [ireg rd; ireg r1]
  | Pxorq_rr rd r1 => node "Pxorq_rr" [ireg rd; ireg r1]
  | Pxorl_ri rd n => node "Pxorl_ri" [ireg rd; int n]
  | Pxorq_ri rd n => node "Pxorq_ri" [ireg rd; long n]
  | Pnotl rd => node "Pnotl" [ireg rd]
  | Pnotq rd => node "Pnotq" [ireg rd]
  | Psall_rcl rd => node "Psall_rcl" [ireg rd]
  | Psalq_rcl rd => node "Psalq_rcl" [ireg rd]
  | Psall_ri rd n => node "Psall_ri" [ireg rd; int n]
  | Psalq_ri rd n => node "Psalq_ri" [ireg rd; int n]
  | Pshrl_rcl rd => node "Pshrl_rcl" [ireg rd]
  | Pshrq_rcl rd => node "Pshrq_rcl" [ireg rd]
  | Pshrl_ri rd n => node "Pshrl_ri" [ireg rd; int n]
  | Pshrq_ri rd n => node "Pshrq_ri" [ireg rd; int n]
  | Psarl_rcl rd => node "Psarl_rcl" [ireg rd]
  | Psarq_rcl rd => node "Psarq_rcl" [ireg rd]
  | Psarl_ri rd n => node "Psarl_ri" [ireg rd; int n]
  | Psarq_ri rd n => node "Psarq_ri" [ireg rd; int n]
  | Pshld_ri rd r1 n => node "Pshld_ri" [ireg rd; ireg r1; int n]
  | Prorl_ri rd n => node "Prorl_ri" [ireg rd; int n]
  | Prorq_ri rd n => node "Prorq_ri" [ireg rd; int n]
  | Pcmpl_rr r1 r2 => node "Pcmpl_rr" [ireg r1; ireg r2]
  | Pcmpq_rr r1 r2 => node "Pcmpq_rr" [ireg r1; ireg r2]
  | Pcmpl_ri r1 n => node "Pcmpl_ri" [ireg r1; int n]
  | Pcmpq_ri r1 n => node "Pcmpq_ri" [ireg r1; long n]
  | Ptestl_rr r1 r2 => node "Ptestl_rr" [ireg r1; ireg r2]
  | Ptestq_rr r1 r2 => node "Ptestq_rr" [ireg r1; ireg r2]
  | Ptestl_ri r1 n => node "Ptestl_ri" [ireg r1; int n]
  | Ptestq_ri r1 n => node "Ptestq_ri" [ireg r1; long n]
  | Pcmov c rd r1 => node "Pcmov" [condition c; ireg rd; ireg r1]
  | Psetcc c rd => node "Psetcc" [condition c; ireg rd]
  | Paddd_ff rd r1 => node "Paddd_ff" [freg rd; freg r1]
  | Psubd_ff rd r1 => node "Psubd_ff" [freg rd; freg r1]
  | Pmuld_ff rd r1 => node "Pmuld_ff" [freg rd; freg r1]
  | Pdivd_ff rd r1 => node "Pdivd_ff" [freg rd; freg r1]
  | Pnegd rd => node "Pnegd" [freg rd]
  | Pabsd rd => node "Pabsd" [freg rd]
  | Pcomisd_ff r1 r2 => node "Pcomisd_ff" [freg r1; freg r2]
  | Pxorpd_f rd => node "Pxorpd_f" [freg rd]
  | Padds_ff rd r1 => node "Padds_ff" [freg rd; freg r1]
  | Psubs_ff rd r1 => node "Psubs_ff" [freg rd; freg r1]
  | Pmuls_ff rd r1 => node "Pmuls_ff" [freg rd; freg r1]
  | Pdivs_ff rd r1 => node "Pdivs_ff" [freg rd; freg r1]
  | Pnegs rd => node "Pnegs" [freg rd]
  | Pabss rd => node "Pabss" [freg rd]
  | Pcomiss_ff r1 r2 => node "Pcomiss_ff" [freg r1; freg r2]
  | Pxorps_f rd => node "Pxorps_f" [freg rd]
  | Pjmp_l l => node "Pjmp_l" [identifier l]
  | Pjmp_s symb sg => node "Pjmp_s" [identifier symb; signature sg]
  | Pjmp_r r sg => node "Pjmp_r" [ireg r; signature sg]
  | Pjcc c l => node "Pjcc" [condition c; identifier l]
  | Pjcc2 c1 c2 l => node "Pjcc2" [condition c1; condition c2; identifier l]
  | Pjmptbl r tbl => node "Pjmptbl" [ireg r; items identifier tbl]
  | Pcall_s symb sg => node "Pcall_s" [identifier symb; signature sg]
  | Pcall_r r sg => node "Pcall_r" [ireg r; signature sg]
  | Pret => "Pret"
  | Pmov_rm_a rd a => node "Pmov_rm_a" [ireg rd; address a]
  | Pmov_mr_a a rs => node "Pmov_mr_a" [address a; ireg rs]
  | Pmovsd_fm_a rd a => node "Pmovsd_fm_a" [freg rd; address a]
  | Pmovsd_mf_a a r1 => node "Pmovsd_mf_a" [address a; freg r1]
  | Plabel l => node "Plabel" [identifier l]
  | Pallocframe sz ofs_ra ofs_link => node "Pallocframe" [number sz; offset ofs_ra; offset ofs_link]
  | Pfreeframe sz ofs_ra ofs_link => node "Pfreeframe" [number sz; offset ofs_ra; offset ofs_link]
  | Pbuiltin ef args res => node "Pbuiltin" [external ef; items builtinarg args; builtinres res]
  | Padcl_ri rd n => node "Padcl_ri" [ireg rd; int n]
  | Padcl_rr rd r2 => node "Padcl_rr" [ireg rd; ireg r2]
  | Paddl_mi a n => node "Paddl_mi" [address a; int n]
  | Paddl_rr rd r2 => node "Paddl_rr" [ireg rd; ireg r2]
  | Pbsfl rd r1 => node "Pbsfl" [ireg rd; ireg r1]
  | Pbsfq rd r1 => node "Pbsfq" [ireg rd; ireg r1]
  | Pbsrl rd r1 => node "Pbsrl" [ireg rd; ireg r1]
  | Pbsrq rd r1 => node "Pbsrq" [ireg rd; ireg r1]
  | Pbswap64 rd => node "Pbswap64" [ireg rd]
  | Pbswap32 rd => node "Pbswap32" [ireg rd]
  | Pbswap16 rd => node "Pbswap16" [ireg rd]
  | Pcfi_adjust n => node "Pcfi_adjust" [int n]
  | Pfmadd132 rd r2 r3 => node "Pfmadd132" [freg rd; freg r2; freg r3]
  | Pfmadd213 rd r2 r3 => node "Pfmadd213" [freg rd; freg r2; freg r3]
  | Pfmadd231 rd r2 r3 => node "Pfmadd231" [freg rd; freg r2; freg r3]
  | Pfmsub132 rd r2 r3 => node "Pfmsub132" [freg rd; freg r2; freg r3]
  | Pfmsub213 rd r2 r3 => node "Pfmsub213" [freg rd; freg r2; freg r3]
  | Pfmsub231 rd r2 r3 => node "Pfmsub231" [freg rd; freg r2; freg r3]
  | Pfnmadd132 rd r2 r3 => node "Pfnmadd132" [freg rd; freg r2; freg r3]
  | Pfnmadd213 rd r2 r3 => node "Pfnmadd213" [freg rd; freg r2; freg r3]
  | Pfnmadd231 rd r2 r3 => node "Pfnmadd231" [freg rd; freg r2; freg r3]
  | Pfnmsub132 rd r2 r3 => node "Pfnmsub132" [freg rd; freg r2; freg r3]
  | Pfnmsub213 rd r2 r3 => node "Pfnmsub213" [freg rd; freg r2; freg r3]
  | Pfnmsub231 rd r2 r3 => node "Pfnmsub231" [freg rd; freg r2; freg r3]
  | Pmaxsd rd r2 => node "Pmaxsd" [freg rd; freg r2]
  | Pminsd rd r2 => node "Pminsd" [freg rd; freg r2]
  | Pmovb_rm rd a => node "Pmovb_rm" [ireg rd; address a]
  | Pmovq_rf rd r1 => node "Pmovq_rf" [ireg rd; freg r1]
  | Pmovsq_mr a rs => node "Pmovsq_mr" [address a; freg rs]
  | Pmovsq_rm rd a => node "Pmovsq_rm" [freg rd; address a]
  | Pmovsb => "Pmovsb"
  | Pmovsw => "Pmovsw"
  | Pmovw_rm rd ad => node "Pmovw_rm" [ireg rd; address ad]
  | Pnop => "Pnop"
  | Prep_movsl => "Prep_movsl"
  | Psbbl_rr rd r2 => node "Psbbl_rr" [ireg rd; ireg r2]
  | Psqrtsd rd r1 => node "Psqrtsd" [freg rd; freg r1]
  | Psubl_ri rd n => node "Psubl_ri" [ireg rd; int n]
  | Psubq_ri rd n => node "Psubq_ri" [ireg rd; long n]
  end.

Definition function (f : Asm.function) : string :=
  node "function" [signature (fn_sig f); items instruction (fn_code f)].

Definition fundef (f : Asm.fundef) : string :=
  match f with
  | Internal f => node "Internal" [function f]
  | External ef => node "External" [external ef]
  end.

Definition global (g : globdef Asm.fundef unit) : string :=
  match g with
  | Gfun f => node "Gfun" [fundef f]
  | Gvar v => node "Gvar" [items initializer (gvar_init v);
      boolean (gvar_readonly v); boolean (gvar_volatile v)]
  end.

Definition definition (g : ident * globdef Asm.fundef unit) : string :=
  node "pair" [identifier (fst g); global (snd g)].

Definition program (p : Asm.program) : string :=
  node "program" [items definition (prog_defs p); items identifier (prog_public p);
    identifier (prog_main p)].
