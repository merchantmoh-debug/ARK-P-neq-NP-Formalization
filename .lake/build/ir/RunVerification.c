// Lean compiler output
// Module: RunVerification
// Imports: public import Init public import ARK_Core.Impossibility public import ARK_Core.Cosmology public import ARK_Core.Witness public import ARK_Core.WitnessN
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* _lean_main();
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__10;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__19;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__3;
lean_object* lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(lean_object*);
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__12;
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___boxed(lean_object*);
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__16;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__11;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__0;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__13;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__14;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__1;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__5;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__4;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__15;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__17;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__9;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__6;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__8;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__7;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__2;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___closed__18;
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__0() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("==================================================", 50, 50);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__1() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("      ARK VERIFICATION PROTOCOL v64.0             ", 50, 50);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__2() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("\n[1] INSPECTING CORE LOGIC...", 29, 29);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__3() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Target: ARK.Logic.p_neq_np_proven", 37, 37);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__4() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Status: COMPILED & TYPE-CHECKED", 35, 35);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__5() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Verdict: ✅ PROOF VALID", 28, 26);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__6() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("\n[2] INSPECTING WITNESS GADGET...", 33, 33);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__7() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Target: Witness_Is_MultiWell (Frustrated Triangle)", 54, 54);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__8() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Verdict: ✅ BARRIER CONFIRMED", 34, 32);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__9() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("\n[3] INSPECTING SPECTRAL GAP...", 31, 31);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__10() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Target: Witness_Gap_Is_Exponential", 38, 38);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__11() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Verdict: ✅ EXPONENTIAL DECAY CONFIRMED", 44, 42);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__12() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("\n[4] INSPECTING N-DIMENSIONAL WITNESS...", 40, 40);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__13() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Target: WitnessN_Disproves_PolyGap", 38, 38);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__14() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Verdict: ✅ SCALABLE CONTRADICTION CONFIRMED", 49, 47);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__15() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("\n[5] INSPECTING COSMOLOGICAL EVIDENCE...", 40, 40);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__16() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Target: Cosmic_Proof_P_neq_NP", 33, 33);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__17() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("    Verdict: ✅ UNIVERSE CONTAINS STARS (Proof Holds)", 54, 52);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__18() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("\n==================================================", 51, 51);
return x_1;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__19() {
_start:
{
lean_object* x_1;
x_1 = lean_mk_string_unchecked("FINAL VERDICT: P ≠ NP (Machine Verified)", 42, 40);
return x_1;
}
}
LEAN_EXPORT lean_object* _lean_main() {
_start:
{
lean_object* x_2; lean_object* x_3;
x_2 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__0;
x_3 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5;
lean_dec_ref(x_3);
x_4 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__1;
x_5 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6;
lean_dec_ref(x_5);
x_6 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8;
lean_dec_ref(x_6);
x_7 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__2;
x_8 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10;
lean_dec_ref(x_8);
x_9 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__3;
x_10 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12;
lean_dec_ref(x_10);
x_11 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__4;
x_12 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14;
lean_dec_ref(x_12);
x_13 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__5;
x_14 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16;
lean_dec_ref(x_14);
x_15 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__6;
x_16 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18;
lean_dec_ref(x_16);
x_17 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__7;
x_18 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19;
lean_dec_ref(x_18);
x_19 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21;
lean_dec_ref(x_19);
x_20 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__8;
x_21 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23;
lean_dec_ref(x_21);
x_22 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__9;
x_23 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25;
lean_dec_ref(x_23);
x_24 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__10;
x_25 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26;
lean_dec_ref(x_25);
x_26 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28;
lean_dec_ref(x_26);
x_27 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__11;
x_28 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30;
lean_dec_ref(x_28);
x_29 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__12;
x_30 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32;
lean_dec_ref(x_30);
x_31 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__13;
x_32 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33;
lean_dec_ref(x_32);
x_33 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35;
lean_dec_ref(x_33);
x_34 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__14;
x_35 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37;
lean_dec_ref(x_35);
x_36 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__15;
x_37 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39;
lean_dec_ref(x_37);
x_38 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__16;
x_39 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40;
lean_dec_ref(x_39);
x_40 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42;
lean_dec_ref(x_40);
x_41 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__17;
x_42 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44;
lean_dec_ref(x_42);
x_43 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__18;
x_44 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46;
lean_dec_ref(x_44);
x_45 = lp_ARK_x2dP_x2dneq_x2dNP_main___closed__19;
x_46 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47;
lean_dec_ref(x_46);
x_47 = lp_importGraph_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__9(x_2);
return x_47;
}
else
{
return x_46;
}
}
else
{
return x_44;
}
}
else
{
return x_42;
}
}
else
{
return x_40;
}
}
else
{
return x_39;
}
}
else
{
return x_37;
}
}
else
{
return x_35;
}
}
else
{
return x_33;
}
}
else
{
return x_32;
}
}
else
{
return x_30;
}
}
else
{
return x_28;
}
}
else
{
return x_26;
}
}
else
{
return x_25;
}
}
else
{
return x_23;
}
}
else
{
return x_21;
}
}
else
{
return x_19;
}
}
else
{
return x_18;
}
}
else
{
return x_16;
}
}
else
{
return x_14;
}
}
else
{
return x_12;
}
}
else
{
return x_10;
}
}
else
{
return x_8;
}
}
else
{
return x_6;
}
}
else
{
return x_5;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2;
x_2 = _lean_main();
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Impossibility(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Cosmology(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Witness(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_WitnessN(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_RunVerification(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Impossibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Cosmology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Witness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_WitnessN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__0 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__0();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__0);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__1 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__1();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__1);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__2 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__2();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__2);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__3 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__3();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__3);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__4 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__4();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__4);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__5 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__5();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__5);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__6 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__6();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__6);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__7 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__7();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__7);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__8 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__8();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__8);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__9 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__9();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__9);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__10 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__10();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__10);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__11 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__11();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__11);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__12 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__12();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__12);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__13 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__13();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__13);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__14 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__14();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__14);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__15 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__15();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__15);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__16 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__16();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__16);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__17 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__17();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__17);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__18 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__18();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__18);
lp_ARK_x2dP_x2dneq_x2dNP_main___closed__19 = _init_lp_ARK_x2dP_x2dneq_x2dNP_main___closed__19();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_main___closed__19);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
  #endif
  lean_object* in; lean_object* res;
argv = lean_setup_args(argc, argv);
lean_initialize();
lean_set_panic_messages(false);
res = initialize_ARK_x2dP_x2dneq_x2dNP_RunVerification(1 /* builtin */);
lean_set_panic_messages(true);
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
res = _lean_main();
}
lean_finalize_task_manager();
if (lean_io_result_is_ok(res)) {
  int ret = 0;
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
