"""New353 synthetic-only zero-pool boundaries; never invoke a compiler or GAME proof."""
import argparse
import copy
from contextlib import redirect_stdout
from contextlib import contextmanager, ExitStack
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

CASE = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(CASE / "tools"))
import match
import function_thunk_profile as profile
import thunk_pool_switch as pool
import match_evidence as evidence
import status

SELECTOR = "canonical-thunks-zero-word-pool-v1"
A = 0x08000000
NAME = "func_08000000"


def bl(site, target):
    offset = target - site - 4
    return struct.pack("<HH", 0xF000 | ((offset >> 12) & 0x7FF), 0xF800 | ((offset >> 1) & 0x7FF))


def fixture(*, interposed=0, data_word=False):
    data = bytearray()
    labels, branches, loads = {}, [], []
    def word(value): data.extend(struct.pack("<H", value))
    def label(name): labels[name] = len(data)
    def branch(opcode, name): branches.append((len(data), opcode, name));word(0)
    def load(register, name): loads.append((len(data),register,name));word(0)
    word(0xB500)
    if data_word: load(2,"object")
    for n in range(interposed): load(n % 3,"pool"+str(n))
    word(0x6813)  # LDR r3,[r2]: actual target remains conditional, never an identity theorem.
    call = len(data);data.extend(bl(A+call, profile.ALIASES["_call_via_r3"]))
    label("comparison");word(0x2801)
    branch(0xD900,"dispatch");branch(0xE000,"default")
    label("dispatch");word(0x0080);load(1,"literal");word(0x1840);word(0x6800);word(0x4687)
    if len(data)%4: word(0)
    for n in range(interposed): label("pool"+str(n));data.extend(struct.pack("<I",0x11111111+n))
    label("literal");data.extend(b"\0"*4)
    label("table");data.extend(b"\0"*8)
    label("case0");word(0x2001);branch(0xE000,"default")
    label("case1");word(0x2002);branch(0xE000,"default")
    label("default");word(0xBC02);word(0x4708)
    if data_word:
        if len(data)%4: word(0)
        label("object");data.extend(struct.pack("<I",0x02001000))
    for site,opcode,name in branches:
        shift=(labels[name]-site-4)//2
        struct.pack_into("<H",data,site,opcode | (shift & (0xFF if opcode==0xD900 else 0x7FF)))
    for site,register,name in loads:
        delta=labels[name]-((site+4)&~3)
        assert delta>=0 and delta%4==0
        struct.pack_into("<H",data,site,0x4800 | register<<8 | delta//4)
    relocations={labels["literal"]:labels["table"],labels["table"]:labels["case0"],labels["table"]+4:labels["case1"]}
    for site,target in relocations.items(): struct.pack_into("<I",data,site,A+target)
    rom=bytearray(profile.END-A)
    rom[:len(data)]=data
    struct.pack_into("<HH",rom,profile.ALIASES["_call_via_r3"]-A,0x4718,0x46C0)
    objects=b'{"g_synthetic":"0x02001000"}' if data_word else None
    literals={labels["object"]:("g_synthetic",0x02001000)} if data_word else {}
    mapping=json.dumps([dict(rom=f"0x{A:08X}",end=f"0x{A+len(data):08X}",mode="thumb")]).encode()
    return dict(data=bytes(data),rom=bytes(rom),labels=labels,switches=relocations,calls={A+call:profile.ALIASES["_call_via_r3"]},objects=objects,literals=literals,mapping=mapping,index=f"{A:08X} {A+len(data):08X} {len(data)}\n".encode())


def leaf(f, *, words=0):
    context={"pool_switch":f["switches"]}
    if words==0: context["interposed_words"]=0
    return match.verify_leaf_instructions(f["data"],A,True,f["calls"],function_thunk_context=context)


def images(f):
    """Synthetic ET_REL/ET_EXEC boundaries with genuine Thumb relocation words."""
    def symbol(name, kind, section, bind, value=0, size=0):
        return dict(name=name,type=kind,section=section,bind=bind,value=value,size=size)
    symbols=[symbol("",0,0,0),symbol("",3,1,0),symbol(NAME,2,1,1,1,len(f["data"])),
             symbol("_call_via_r3",2,0,1)]
    original=bytearray(f["data"]);relocations=[]
    for site in f["calls"]:
        offset=site-A;original[offset:offset+4]=bl(site,site);relocations.append((offset,3<<8|10))
    for offset,addend in f["switches"].items():
        struct.pack_into("<I",original,offset,addend);relocations.append((offset,1<<8|2))
    if f["literals"]:
        symbols.append(symbol("g_synthetic",1,0,1))
        for offset in f["literals"]:
            struct.pack_into("<I",original,offset,0);relocations.append((offset,4<<8|2))
    encoded=b"".join(struct.pack("<II",*record) for record in relocations)
    sections=[(0,0,0,0,0,0,0,0,0,0),(0,1,6,0,0,len(original),0,0,4,0),
              (0,2,0,0,0,0,0,0,4,16),(0,9,0,0,0,len(encoded),2,1,4,8)]
    before=dict(type=1,text=bytes(original),text_index=1,symbols=symbols,sections=sections,
                relocations=[3],symbol_tables={2:symbols},section_data={3:encoded})
    after=copy.deepcopy(before);after.update(type=2,text=f["data"],relocations=[])
    after["sections"][1]=(0,1,6,A,0,len(original),0,0,4,0)
    after["symbols"][1]["value"]=A;after["symbols"][2]["value"]=A|1
    after["symbols"][3].update(section=0xFFF1,value=profile.ALIASES["_call_via_r3"]|1)
    if f["literals"]:after["symbols"][4].update(section=0xFFF1,value=0x02001000)
    return before,after


def bindings(f,image):
    switches={}
    calls,functions,literals=profile.original_bindings(image,A,f["mapping"],f["rom"],f["objects"],
        switch_relocations=switches,selector=SELECTOR)
    targets={"_call_via_r3":profile.ALIASES["_call_via_r3"]}
    if literals:targets["g_synthetic"]=0x02001000
    return calls,targets,literals,functions,switches


@contextmanager
def synthetic_environment(*, interposed=0):
    """Only compiler/ELF/plausibility/subprocess boundaries are mocked."""
    f=fixture(data_word=True,interposed=interposed);before,after=images(f)
    scratch=CASE/"scratch";scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="synthetic_",dir=scratch) as directory:
        root=Path(directory)
        for child in ("src","include","config","symbols","docs/match","build"):(root/child).mkdir(parents=True,exist_ok=True)
        (root/"src/08000000.c").write_text("unsigned func_08000000(void *record) { return *(unsigned *)record; }\n")
        (root/"config/functions.json").write_bytes(f["mapping"])
        (root/"config/data_symbols.json").write_bytes(f["objects"])
        (root/"symbols/functions.txt").write_bytes(f["index"])
        (root/"synthetic.rom").write_bytes(f["rom"])
        commands=[];compiled=[]
        class FakeRunner:
            def __init__(self,*args,**kwargs):pass
            @contextmanager
            def workspace(self):
                with tempfile.TemporaryDirectory(prefix="mock_link_",dir=scratch) as work:yield work
            def read_binary(self,path):
                if str(path).endswith("f.elf"):return b"SYNTHETIC_LINKED_ELF_BOUNDARY"
                if str(path).endswith("f.linked.bin"):return f["data"]
                return Path(path).read_bytes()
            def write_text(self,path,value):Path(path).write_text(value)
            def sh(self,command):commands.append(command)
        def compile_boundary(runner,workspace,args,source_root,address,relative,thumb=True):
            assert address==A and thumb and args.flags==match.DEFAULT_FLAGS
            compiled.append(str(source_root))
            (Path(workspace)/"f.i").write_bytes((Path(source_root)/relative).read_bytes())
            return b"SYNTHETIC_ORIGINAL_ELF_BOUNDARY",before["text"],copy.deepcopy(before)
        def elf_boundary(raw):
            if raw!=b"SYNTHETIC_LINKED_ELF_BOUNDARY":raise AssertionError("unexpected original or linked ELF")
            return copy.deepcopy(after)
        def plausible_boundary(command,*args):
            assert "--json" in command
            return SimpleNamespace(returncode=0,stdout=json.dumps(dict(findings=[],total=0,addr="0x08000000",hand_asm_allowed=False,allow_entry=None)),stderr="")
        exists=os.path.exists
        with ExitStack() as stack:
            stack.enter_context(patch.dict(os.environ,{"FFTA_ROM":str(root/"synthetic.rom"),"TMPDIR":str(scratch),"TEMP":str(scratch),"TMP":str(scratch)}))
            stack.enter_context(patch.object(match,"Runner",FakeRunner))
            stack.enter_context(patch.object(match,"compile_object",compile_boundary))
            stack.enter_context(patch.object(match,"elf_image",elf_boundary))
            stack.enter_context(patch.object(match,"_run_replay_process",plausible_boundary))
            stack.enter_context(patch.object(os.path,"exists",lambda p:True if str(p)==str(CASE/"tools/plausible.py") else exists(p)))
            yield SimpleNamespace(root=root,f=f,commands=commands,compiled=compiled,before=before,after=after)


class ZeroInterposedThunks353(unittest.TestCase):
    def test_zero_context_admits_complete_synthetic_R3_CFG(self):
        f=fixture(data_word=True)
        instructions=leaf(f)
        self.assertTrue(instructions)
        self.assertEqual(pool.record(f["data"],A,f["switches"],instructions,interposed_words=0)["pool"],[])

    def test_legacy_five_word_policy_and_default_refusal_remain_distinct(self):
        f=fixture(interposed=5)
        instructions=leaf(f,words=5)
        self.assertEqual(len(pool.record(f["data"],A,f["switches"],instructions)["pool"]),5)
        zero=fixture()
        with self.assertRaises(ValueError):leaf(zero,words=5)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(zero["data"],A,True,zero["calls"],switch_relocations=zero["switches"])
        with self.assertRaises(ValueError):leaf(f)
        for value in (False,True,1,4,6,None):
            with self.subTest(value=value),self.assertRaises(ValueError):pool.pool_words(value)

    def test_zero_policy_rejects_malformed_CFG_frame_and_thunk_composition(self):
        f=fixture()
        for offset,value in ((f["labels"]["comparison"],0x2802),
                             (f["labels"]["comparison"]+2,0xD800),
                             (0,0xB081),(f["labels"]["default"],0xBC01)):
            damaged=copy.deepcopy(f);body=bytearray(f["data"]);struct.pack_into("<H",body,offset,value);damaged["data"]=bytes(body)
            with self.subTest(offset=offset,value=value),self.assertRaises(ValueError):leaf(damaged)
        for context in ({"interposed_words":False},{"interposed_words":5},{"buffer":{}},
                        {"interposed_words":0,"pool_switch":f["switches"],"buffer":{}}):
            with self.subTest(context=context),self.assertRaises(ValueError):
                match.verify_leaf_instructions(f["data"],A,True,f["calls"],function_thunk_context=context)
        for calls in ({},{A:profile.ALIASES["_call_via_r2"]},
                      {A:profile.ALIASES["_call_via_r3"],A+4:profile.ALIASES["_call_via_r2"]}):
            with self.subTest(calls=calls),self.assertRaises(ValueError):profile.verify_pool_calls(calls,0)
        with self.assertRaises(ValueError):profile.check_pool_opt_in(0,False)
        with self.assertRaises(ValueError):profile.check_pool_opt_in(False,True)

    def test_original_ELF_and_linked_whole_body_enforce_relocation_identity(self):
        f=fixture(data_word=True);before,after=images(f)
        calls,targets,literals,functions,switches=bindings(f,before)
        self.assertEqual(switches,f["switches"]);self.assertEqual(literals,f["literals"])
        kwargs=dict(data_relocations=literals,function_relocations=functions,switch_relocations=switches,
                    function_thunks=True,thunk_pool_words=0)
        self.assertEqual(match.linked_function_bytes(before,after,NAME,A,calls,targets,**kwargs),f["data"])
        for mutation in ("kind","BL_addend","duplicate_symbol","data_type","switch_addend"):
            broken=copy.deepcopy(before)
            if mutation=="kind":
                data=bytearray(broken["section_data"][3]);struct.pack_into("<I",data,4,3<<8|1);broken["section_data"][3]=bytes(data)
            elif mutation=="duplicate_symbol":broken["symbols"].append(copy.deepcopy(broken["symbols"][3]))
            elif mutation=="data_type":broken["symbols"][4]["type"]=2
            else:
                data=bytearray(broken["text"])
                if mutation=="BL_addend":
                    site=next(iter(calls));data[site-A:site-A+4]=bl(site,site+2)
                else:struct.pack_into("<I",data,f["labels"]["literal"],1)
                broken["text"]=bytes(data)
            with self.subTest(original=mutation),self.assertRaises(ValueError):bindings(f,broken)
        for mutation in ("unrelocated_byte","data_word","case_word","function_size","veneer","symbol_type","relocation"):
            broken=copy.deepcopy(after)
            if mutation=="function_size":broken["symbols"][2]["size"]-=2
            elif mutation=="veneer":broken["symbols"].append(dict(name="veneer",type=2,section=1,bind=0,value=A|1,size=2))
            elif mutation=="symbol_type":broken["symbols"][4]["type"]=2
            elif mutation=="relocation":broken["relocations"]=[3]
            else:
                data=bytearray(broken["text"])
                offset={"unrelocated_byte":f["labels"]["case0"],"data_word":f["labels"]["object"],"case_word":f["labels"]["table"]}[mutation]
                data[offset]^=1;broken["text"]=bytes(data)
            with self.subTest(linked=mutation),self.assertRaises(ValueError):
                match.linked_function_bytes(before,broken,NAME,A,calls,targets,**kwargs)

    def test_manifest_binds_exact_zero_selector_sources_runtime_data_and_extent(self):
        f=fixture(data_word=True);instructions=leaf(f)
        manifest=profile.make_manifest(f["calls"],{},f["literals"],A,f["rom"],f["objects"],instructions,selector=SELECTOR)
        self.assertEqual(manifest["selector"],SELECTOR)
        self.assertEqual(manifest["pool_switch"]["schema"],pool.ZERO_SCHEMA)
        self.assertTrue(profile.verify(f["data"],A,f["rom"],f["mapping"],f["index"],f["objects"],manifest))
        for mutation in ("selector","source","pool","dependency","extra","data"):
            broken=copy.deepcopy(manifest)
            if mutation=="selector":broken["selector"]=profile.SELECTOR
            elif mutation=="source":broken["producer_source_sha256"]["match.py"]="0"*64
            elif mutation=="pool":broken["pool_switch"]["schema"]=pool.SCHEMA
            elif mutation=="dependency":broken["dependencies"][0][3]="0"*64
            elif mutation=="extra":broken["buffer"]=[]
            else:broken["data"][0][2]=4
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                profile.verify(f["data"],A,f["rom"],f["mapping"],f["index"],f["objects"],broken)
        for field in ("mapping","index","objects","rom"):
            changed=dict(f)
            if field=="mapping":changed[field]=b"[]"
            elif field=="index":changed[field]=f"{A:08X} {A+2:08X} 2\n".encode()
            elif field=="objects":changed[field]=b'{"g_synthetic":"0x02001004"}'
            else:
                data=bytearray(f["rom"]);data[profile.ALIASES["_call_via_r3"]-A]^=1;changed[field]=bytes(data)
            with self.subTest(field=field),self.assertRaises(ValueError):
                profile.verify(f["data"],A,changed["rom"],changed["mapping"],changed["index"],changed["objects"],manifest)

    def test_explicit_CLI_report_fresh_source_replay_and_status_selector_roundtrip(self):
        with synthetic_environment() as env:
            command=["match.py","--root",str(env.root),"--function-address-profile",SELECTOR,"0x08000000"]
            with patch.object(sys,"argv",command),redirect_stdout(io.StringIO()) as output:
                self.assertEqual(match.main(),0)
            self.assertIn("verdict MATCH - byte identical",output.getvalue())
            report_path=env.root/"docs/match/08000000.md";report=report_path.read_text()
            self.assertEqual(profile.selector_for_report(report),SELECTOR)
            self.assertTrue(evidence.report_matches(report,env.root,A))
            self.assertGreaterEqual(len(env.compiled),3) # original, issuing replay, report replay
            self.assertEqual(len(env.commands),3*len(env.compiled))
            (CASE/"synthetic-zero-pool-report.md").write_text(report)
            calls=[]
            def status_boundary(command,**kwargs):
                calls.append(command)
                return SimpleNamespace(returncode=0,stdout=f"extent    {len(env.f['data'])} bytes\nverdict MATCH - byte identical\n",stderr="")
            with patch.object(status.subprocess,"run",status_boundary):
                result=status.collect(str(env.root),True,quiet=True)
            self.assertEqual(result[1],1);self.assertEqual(result[4],[])
            self.assertEqual(len(calls),1)
            self.assertEqual(calls[0][calls[0].index("--function-address-profile")+1],SELECTOR)
            self.assertEqual(calls[0][calls[0].index("--root")+1],str(env.root))
            (CASE/"synthetic-mocked-commands.json").write_text(json.dumps(dict(shell_commands=env.commands,status_commands=calls,compiler_boundary_calls=len(env.compiled)),indent=2)+"\n")

    def test_forged_report_policy_and_stale_inputs_refuse_before_status_execution(self):
        with synthetic_environment() as env:
            with patch.object(sys,"argv",["match.py","--root",str(env.root),"--function-address-profile",SELECTOR,"0x08000000"]),redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(),0)
            report_path=env.root/"docs/match/08000000.md";report=report_path.read_text()
            variants=[report.replace(SELECTOR,"unsupported-thunks-v1"),
                      report.replace(f"* function-address thunks: {SELECTOR}",f"* function-address thunks: {profile.SELECTOR}"),
                      report+f"\n* function-address thunks: {SELECTOR}\n",
                      report.replace(profile.ZERO_SCHEMA,profile.SCHEMA),
                      report.replace('"selector":"'+SELECTOR+'"','"selector":"'+profile.SELECTOR+'"'),
                      report+"\n* buffer ABI: forged\n"]
            for damaged in variants:
                self.assertFalse(evidence.report_matches(damaged,env.root,A))
                report_path.write_text(damaged)
                with patch.object(status.subprocess,"run",side_effect=AssertionError("forged report dispatched")):
                    result=status.collect(str(env.root),True,quiet=True)
                self.assertEqual(result[1],0);self.assertTrue(result[4])
            report_path.write_text(report)
            for relative in ("src/08000000.c","config/data_symbols.json","symbols/functions.txt"):
                path=env.root/relative;saved=path.read_bytes();path.write_bytes(saved+b" ")
                self.assertFalse(evidence.report_matches(report,env.root,A));path.write_bytes(saved)
            count=len(env.compiled)
            with patch.object(sys,"argv",["match.py","--root",str(env.root),"--function-address-profile","unsupported-thunks-v1","0x08000000"]),self.assertRaises(SystemExit) as error:
                match.main()
            self.assertEqual(error.exception.code,2);self.assertEqual(len(env.compiled),count)

    def test_standalone_legacy_CLI_and_status_use_only_repo_local_sources(self):
        """Distinct portability case; also keeps the five-word report schema unchanged."""
        with synthetic_environment(interposed=5) as env:
            with patch.object(sys,"argv",["match.py","--root",str(env.root),"--function-address-profile",profile.SELECTOR,"0x08000000"]),redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(),0)
            report=(env.root/"docs/match/08000000.md").read_text()
            self.assertEqual(profile.selector_for_report(report),profile.SELECTOR)
            self.assertIn(f"* verification: `{profile.SCHEMA}`",report)
            self.assertNotIn('"producer_source_sha256"',report)
            self.assertNotIn('"selector"',report)
            self.assertTrue(evidence.report_matches(report,env.root,A))
            calls=[]
            def status_boundary(command,**kwargs):
                calls.append(command)
                return SimpleNamespace(returncode=0,stdout=f"extent {len(env.f['data'])} bytes\nverdict MATCH - byte identical\n",stderr="")
            with patch.object(status.subprocess,"run",status_boundary):
                result=status.collect(str(env.root),True,quiet=True)
            self.assertEqual(result[1],1);self.assertEqual(result[4],[])
            self.assertEqual(calls[0][calls[0].index("--function-address-profile")+1],profile.SELECTOR)
            loaded={name:str(Path(module.__file__).resolve()) for name,module in list(sys.modules.items())
                    if getattr(module,"__file__",None) and Path(module.__file__).suffix==".py"
                    and Path(module.__file__).name in {path.name for path in (CASE/"tools").glob("*.py")}}
            self.assertIn("match",loaded);self.assertIn("status",loaded)
            for name,path in loaded.items():
                self.assertEqual(Path(path).parent,(CASE/"tools").resolve(),name)
            (CASE/"portability-loaded-modules.json").write_text(json.dumps(loaded,indent=2,sort_keys=True)+"\n")


if __name__ == "__main__": unittest.main()
