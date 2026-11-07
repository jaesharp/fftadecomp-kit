"""Closed C-AST/retained-machine relation, conditional on explicit C/ABI memory facts.

The parser accepts a deliberately bounded C subset. Full AST equality to the
typed algorithm is required; function/data addresses never select acceptance.
No compiler, ELF qualifier, machine interpreter or earlier proof is invoked.
"""
import hashlib
import json
import re

import palette_value_composition as ir

SELECTOR='conditional-palette-source-machine-correspondence-v1'
TOKEN=re.compile(r'\s+|/\*.*?\*/|//[^\n]*|0[xX][0-9a-fA-F]+|[0-9]+|[A-Za-z_][A-Za-z_0-9]*|\+\+|\+=|!=|<=|>=|==|<<|>>|[{}()[\];,*&|+\-=<>]',re.S)
IDENT=re.compile(r'[A-Za-z_][A-Za-z_0-9]*\Z')
KEYWORDS=set('auto break case char const continue default do double else enum extern float for goto if inline int long register restrict return short signed sizeof static struct switch typedef union unsigned void volatile while _Bool _Complex _Imaginary asm typeof'.split())
PRECEDENCE={'=':1,'+=':1,'|':2,'&':3,'==':4,'!=':4,'<':5,'>':5,'<=':5,'>=':5,'<<':6,'>>':6,'+':7,'-':7,'*':8}


def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def tokens(source):
    if type(source) is not bytes or not 0<len(source)<=32768:raise ValueError('source must be a bounded immutable C byte string')
    try:text=source.decode('ascii')
    except UnicodeDecodeError as exc:raise ValueError('source grammar requires ASCII') from exc
    # Translation-phase splices/trigraphs and directives must not change what
    # this non-preprocessing parser sees, including inside line comments.
    if '\\' in text or '??' in text or '\x00' in text:raise ValueError('source translation-phase syntax is outside closed grammar')
    result=[];offset=0
    while offset<len(text):
        found=TOKEN.match(text,offset)
        if not found:raise ValueError('source has unsupported token at byte '+str(offset))
        token=found.group();offset=found.end()
        if token.isspace() or token.startswith(('/*','//')):continue
        if token[0].isdigit():
            if len(token)>1 and token[0]=='0' and token[1] not in 'xX':raise ValueError('source octal literal is outside closed grammar')
            token=int(token,16 if token.lower().startswith('0x') else 10)
            if token>0x7fffffff:raise ValueError('source integer literal exceeds signed target int')
        result.append(token)
        if len(result)>4096:raise ValueError('source token budget exceeded')
    return result+['<eof>']


class Parser:
    def __init__(self,source):self.items=tokens(source);self.position=0;self.aliases={};self.depth=0

    def peek(self):return self.items[self.position]

    def pop(self,expected=None):
        token=self.peek()
        if expected is not None and token!=expected:raise ValueError('source grammar expected '+repr(expected)+', got '+repr(token))
        self.position+=1
        return token

    def identifier(self):
        token=self.pop()
        if type(token) is not str or not IDENT.fullmatch(token) or token in KEYWORDS or token.startswith('__'):raise ValueError('source requires ordinary identifier')
        return token

    def type(self):
        qualifiers=()
        if self.peek()=='const':self.pop();qualifiers=('const',)
        name=self.pop();base='void' if name=='void' else self.aliases.get(name)
        if base is None:raise ValueError('source type is not a declared closed alias')
        pointers=0
        while self.peek()=='*':self.pop();pointers+=1
        if pointers>1:raise ValueError('source has unsupported pointer depth')
        return base,qualifiers,pointers

    def declaration(self,allow_initializer=True):
        base,qualifiers,pointers=self.type();name=self.identifier();dimensions=[]
        while self.peek()=='[':
            self.pop();dimension=None if self.peek()==']' else self.pop()
            if dimension is not None and (type(dimension) is not int or dimension<=0):raise ValueError('source array dimension is not a positive integer')
            self.pop(']');dimensions.append(dimension)
            if len(dimensions)>2:raise ValueError('source array depth exceeds closed grammar')
        initializer=None
        if allow_initializer and self.peek()=='=':
            self.pop()
            if self.peek()=='{':
                self.pop();values=[self.expression()]
                while self.peek()==',':self.pop();values.append(self.expression())
                self.pop('}');initializer=('initializer',tuple(values))
            else:initializer=self.expression()
        return ('decl',name,(base,qualifiers,pointers,tuple(dimensions)),initializer)

    def parameters(self):
        self.pop('(');result=[]
        if self.peek()!=')':
            result.append(self.declaration(False))
            while self.peek()==',':self.pop();result.append(self.declaration(False))
        self.pop(')')
        if len({row[1] for row in result})!=len(result):raise ValueError('source parameter names collide')
        return tuple(result)

    def expression(self,minimum=1):
        self.depth+=1
        if self.depth>64:raise ValueError('source expression nesting exceeds bound')
        token=self.pop()
        if type(token) is int:left=('int',token)
        elif token=='(':
            left=self.expression();self.pop(')')
        elif token in ('&','*','-','+'):
            left=('unary',token,self.expression(9))
        elif type(token) is str and IDENT.fullmatch(token) and token not in KEYWORDS:left=('id',token)
        else:raise ValueError('source expression is outside closed grammar')
        while True:
            token=self.peek()
            if token=='[':
                self.pop();index=self.expression();self.pop(']');left=('index',left,index)
            elif token=='++':self.pop();left=('postincrement',left)
            elif token in PRECEDENCE and PRECEDENCE[token]>=minimum:
                self.pop();precedence=PRECEDENCE[token]
                right=self.expression(precedence if token in ('=','+=') else precedence+1)
                left=('assignment' if token in ('=','+=') else 'binary',token,left,right)
            else:break
        self.depth-=1
        return left

    def statement(self):
        self.depth+=1
        if self.depth>64:raise ValueError('source statement nesting exceeds bound')
        token=self.peek()
        if token=='{':
            self.pop();body=[]
            while self.peek()!='}':body.append(self.statement())
            self.pop();result=('block',tuple(body))
        elif token=='if':
            self.pop();self.pop('(');condition=self.expression();self.pop(')');yes=self.statement();no=None
            if self.peek()=='else':self.pop();no=self.statement()
            result=('if',condition,yes,no)
        elif token=='for':
            self.pop();self.pop('(');initial=self.expression();self.pop(';');condition=self.expression();self.pop(';')
            step=self.expression();self.pop(')');result=('for',initial,condition,step,self.statement())
        elif token in self.aliases or token=='const':result=self.declaration();self.pop(';')
        else:result=('expression',self.expression());self.pop(';')
        self.depth-=1
        return result

    def parse(self):
        globals_=[];prototypes=[];functions=[];names=set()
        while self.peek()!='<eof>':
            if self.peek()=='typedef':
                self.pop();sign=self.pop();kind=self.pop();name=self.identifier();self.pop(';')
                types={('unsigned','char'):'u8',('unsigned','short'):'u16',('signed','short'):'s16',('unsigned','int'):'u32'}
                if (sign,kind) not in types or name in names:raise ValueError('source typedef is unsupported or duplicated')
                self.aliases[name]=types[sign,kind];names.add(name);continue
            external=self.peek()=='extern'
            if external:self.pop()
            declaration=self.declaration(False);name=declaration[1]
            if name in names:raise ValueError('source global names collide')
            names.add(name)
            if self.peek()=='(':
                parameters=self.parameters()
                if external:self.pop(';');prototypes.append((declaration,parameters))
                else:functions.append((declaration,parameters,self.statement()))
            else:
                if not external:raise ValueError('source has extra storage definition')
                self.pop(';');globals_.append(declaration)
        return {'aliases':self.aliases,'globals':tuple(globals_),'prototypes':tuple(prototypes),'functions':tuple(functions)}


def ident(name):return ('id',name)
def integer(value):return ('int',value)
def binary(op,a,b):return ('binary',op,a,b)
def index(name,subscript):return ('index',ident(name),subscript)
def assign(target,value,op='='):return ('expression',('assignment',op,target,value))
def block(*statements):return ('block',tuple(statements))
def declaration(name,base,pointers=0,dimensions=(),initializer=None):return ('decl',name,(base,(),pointers,dimensions),initializer)


def algorithm_ast(names):
    first,count,red,green,blue,restore,channels,changes,last,i,j,palette,history=names
    channel=index(channels,ident(j));delta=('unary','*',index(changes,ident(j)))
    history_cell=('index',index(history,ident(i)),ident(j));palette_cell=index(palette,ident(i))
    adjustment=('if',binary('!=',delta,integer(0)),block(
        assign(channel,delta,'+='),
        ('if',binary('<',channel,integer(0)),assign(channel,integer(0)),
         ('if',binary('>',channel,integer(31)),assign(channel,integer(31)),None))),None)
    def loop(variable,initial,op,limit,body):
        return ('for',('assignment','=',ident(variable),initial),binary(op,ident(variable),limit),('postincrement',ident(variable)),body)
    packed=binary('|',binary('|',binary('<<',index(channels,integer(1)),integer(5)),index(channels,integer(0))),
                  binary('<<',index(channels,integer(2)),integer(10)))
    normal=loop(i,ident(first),'<=',ident(last),block(
        assign(index(channels,integer(0)),binary('&',palette_cell,integer(31))),
        assign(index(channels,integer(1)),binary('>>',binary('&',palette_cell,integer(992)),integer(5))),
        assign(index(channels,integer(2)),binary('>>',binary('&',palette_cell,integer(31744)),integer(10))),
        loop(j,integer(0),'<',integer(3),block(assign(history_cell,channel),adjustment)),assign(palette_cell,packed)))
    restoring=loop(i,ident(first),'<=',ident(last),block(
        loop(j,integer(0),'<',integer(3),block(assign(channel,history_cell),adjustment)),assign(palette_cell,packed)))
    return block(declaration(channels,'s16',dimensions=(3,)),
        declaration(changes,'s16',1,(3,),('initializer',tuple(('unary','&',ident(name)) for name in (red,green,blue)))),
        declaration(last,'u16'),declaration(i,'u16'),declaration(j,'u16'),
        assign(ident(last),binary('-',binary('+',ident(first),ident(count)),integer(1))),
        ('if',binary('>',ident(last),integer(511)),assign(ident(last),integer(511)),None),
        ('if',binary('==',ident(restore),integer(0)),block(normal),block(restoring)))


def check_prototype_scope(parsed):
    for _,parameters in parsed['prototypes']:
        if any(row[1] in parsed['aliases'] for row in parameters):
            raise ValueError('source prototype parameter hides a typedef in prototype scope')


def close_source(source):
    parsed=Parser(source).parse()
    check_prototype_scope(parsed)
    if sorted(parsed['aliases'].values())!=['s16','u16','u32','u8'] or len(parsed['globals'])!=2 or len(parsed['prototypes'])!=1 or len(parsed['functions'])!=1:
        raise ValueError('source translation unit differs from closed declarations')
    palette,history=parsed['globals']
    if palette!=declaration(palette[1],'u16',dimensions=(None,)) or history!=declaration(history[1],'u8',dimensions=(None,12)):
        raise ValueError('source palette/history element types or row stride differ')
    prototype,parameters=parsed['prototypes'][0]
    if prototype!=declaration(prototype[1],'void',1) or len(parameters)!=3 or \
            [row[2] for row in parameters]!=[('void',(),1,()),('void',('const',),1,()),('u32',(),0,())]:
        raise ValueError('source unused helper declaration differs')
    function,parameters,body=parsed['functions'][0]
    if function!=declaration(function[1],'void') or len(parameters)!=6 or any(
            row!=declaration(row[1],base) for row,base in zip(parameters,('u16','u16','s16','s16','s16','u8'))):
        raise ValueError('source exact six-argument signature differs')
    if body[0]!='block' or len(body[1])!=8 or any(row[0]!='decl' for row in body[1][:5]):
        raise ValueError('source local declarations or whole-body shape differ')
    names=[row[1] for row in parameters]+[row[1] for row in body[1][:5]]+[palette[1],history[1]]
    if len(set(names))!=len(names) or set(names)&(set(parsed['aliases'])|{function[1],prototype[1]}):
        raise ValueError('source roles collide or shadow a required declaration')
    expected=algorithm_ast(names)
    if body!=expected:raise ValueError('source AST differs from closed typed palette algorithm')
    return {'function':function[1],'parameter_names':names[:6],'parameter_types':['u16','u16','s16','s16','s16','u8'],
        'locals':names[6:11],'palette':palette[1],'history':history[1],'history_stride':12,
        'unused_helper_prototype':prototype[1],'AST_sha256':digest(parsed),'body_AST_sha256':digest(body),
        'source_sha256':hashlib.sha256(source).hexdigest(),'source_bytes':len(source),
        'pointer_initializer_order':names[2:5],'root_return_type':'void','external_calls_in_C_body':0}


def frozen_tuple(value):
    return tuple(frozen_tuple(item) for item in value) if isinstance(value,(list,tuple)) else value


def expected_values(palette,history):
    first=ir.low(('input','r0',32),16);count=ir.low(('input','r1',32),16)
    deltas=[ir.low(('input',name,32),16) for name in ('r2','r3','incoming0')]
    restore=ir.low(('input','incoming4',32),8)
    last=ir.low(ir.add(first,count,ir.constant(-1)),16);i=('input','index',9)
    palette_address=ir.add(ir.constant(palette),ir.multiply(2,i))
    history_addresses=[ir.add(ir.constant(history),ir.multiply(12,i),ir.constant(j)) for j in range(3)]
    modes={}
    for mode in ('normal','restore'):
        reads=[('read',j,2 if mode=='normal' else 1,palette_address if mode=='normal' else history_addresses[j]) for j in range(3)]
        channels=[ir.low(reads[0],5),('extract',reads[1],5,5),('extract',reads[2],10,5)] if mode=='normal' else reads
        updated=[ir.adjust(value,delta) for value,delta in zip(channels,deltas)]
        effects=[('external-read',read[3],read[2],read) for read in reads]
        if mode=='normal':effects.extend(('external-write',address,1,value) for address,value in zip(history_addresses,channels))
        effects.append(('external-write',palette_address,2,ir.pack_channels(updated)))
        modes[mode]={'events':tuple(effects),'inputs':tuple(channels),'outputs':tuple(updated),'next':ir.add(i,ir.constant(1))}
    return first,last,restore,modes


def correlate(machine,inventory,model):
    if machine.get('schema')!=ir.SELECTOR or machine.get('conditional_owner_machine_value_trace') is not True or \
            machine.get('physical_memory_permission') is not False or machine.get('source_or_ELF_admission') is not False:
        raise ValueError('source requires the retained conditional machine certificate')
    if inventory.get('schema')!='thumb-compiler-local-copy-elf-inventory-v1' or inventory.get('inventory_only') is not True:
        raise ValueError('source requires the retained original ELF binding inventory')
    for key in ('address','end','instructions','ROM_sha256'):
        if machine[key]!=inventory[key]:raise ValueError('source machine and original inventory context differ')
    if machine['body_sha256']!=inventory['linked_text_sha256']:raise ValueError('source machine and original FUNC bytes differ')
    data={};calls=[]
    for offset,kind,name,address in inventory['relocations']:
        if kind==2:
            if name in data and data[name]!=address:raise ValueError('source data has inconsistent canonical binding')
            data[name]=address
        elif kind==10:calls.append((offset,name,address))
        else:raise ValueError('source original inventory contains an unrelated relocation')
    if set(data)!={model['palette'],model['history']} or len(calls)!=1 or calls[0][1]!='memcpy' or calls[0][2]!=inventory['helper_identity'][0]:
        raise ValueError('source declared symbols do not match genuine original bindings')
    first,last,restore,modes=expected_values(data[model['palette']],data[model['history']])
    iterations={row['mode']:row for row in machine['iterations']}
    if len(machine['iterations'])!=2 or set(iterations)!=set(modes):raise ValueError('source machine branch modes differ')
    for mode,expected in modes.items():
        actual=iterations[mode]
        effects=tuple((row[0],frozen_tuple(row[2]),row[3],frozen_tuple(row[4])) for row in actual['events'])
        if effects!=expected['events'] or frozen_tuple(actual['channel_inputs'])!=expected['inputs'] or \
                frozen_tuple(actual['channel_outputs'])!=expected['outputs'] or frozen_tuple(actual['next_index'])!=expected['next'] or \
                frozen_tuple(actual['limit'])!=('input','limit',9) or actual['index_domain']!=[0,511]:
            raise ValueError('source values or ordered accesses differ from machine iteration')
        if not actual['non_channel_memory_unchanged'] or not actual['distinct_external_read_tokens_preserved']:
            raise ValueError('source iteration lacks retained frame/read independence')
    entries=set()
    for limited,limit in ((False,last),(True,ir.constant(511))):
        minimum=('ugt' if limited else 'ule',last,ir.constant(511))
        for mode in modes:
            selected=('eq' if mode=='normal' else 'ne',restore,ir.constant(0))
            for entered in (False,True):
                guard=('ule' if entered else 'ugt',first,limit)
                entries.add((frozenset((minimum,selected,guard)),iterations[mode]['header'] if entered else machine['epilogue_from_retained_frame'][0],limit))
    observed={(frozenset(frozen_tuple(row['guards'])),row['stop'],frozen_tuple(row['last'])) for row in machine['prefix_paths']}
    if len(machine['prefix_paths'])!=8 or entries!=observed:raise ValueError('source wrapped min, restore selection or entry guard differs')
    return {'data_bindings':data,'entry_cases':8,'normal_external_events':len(modes['normal']['events']),
        'restore_external_events':len(modes['restore']['events']),'source_function':model['function'],
        'compiler_generated_copy':{'site':inventory['address']+calls[0][0],'target':calls[0][2],
            'C_calls':0,'effects_from_reused023_and056_only':True}}


def verify(source,machine,inventory,*,selector,reuse_authority):
    if selector!=SELECTOR or type(reuse_authority) is not dict or reuse_authority.get('independently_established_frozen_certificates') is not True:
        raise ValueError('source bridge needs explicit selector and independent retained authority')
    if reuse_authority.get('machine_sha256')!=digest(machine) or reuse_authority.get('inventory_sha256')!=digest(inventory) or \
            reuse_authority.get('original_source_sha256')!=hashlib.sha256(source).hexdigest() or reuse_authority.get('original_source_and_object_lineage_authenticated') is not True:
        raise ValueError('source bridge frozen source/object/certificate identity differs')
    model=close_source(source);relation=correlate(machine,inventory,model)
    return {'schema':SELECTOR,'source':model,'machine_address':machine['address'],'machine_end':machine['end'],
        'machine_body_sha256':machine['body_sha256'],'ROM_sha256':machine['ROM_sha256'],'relation':relation,
        'entry_argument_transport':[
            {'parameter':model['parameter_names'][i],'C_type':model['parameter_types'][i],
             'machine_bits':location,'width':width} for i,(location,width) in enumerate(
                 [('R0',16),('R1',16),('R2',16),('R3',16),('incoming word at entrySP+0',16),('incoming word at entrySP+4',8)])],
        'C_definedness':{
            'first_plus_count_minus_one_signed_int_range':[-1,131069],
            'last_unsigned16_conversion':'defined modulo65536, then min(last,511)',
            'inner_counter_values':[0,3],'executed_outer_index_range':[0,511],'outer_successor_range':[1,512],
            'channel_before_add_normal_range':[0,31],'channel_before_add_restore_range':[0,255],
            'promoted_delta_range':[-32768,32767],'promoted_channel_plus_delta_range':[-32768,33022],
            'compound_assignment_conversion':'implementation-defined out-of-range signed-short result must be low16 interpreted signed, without signal',
            'after_nonzero_delta_clamp_range':[0,31],'zero_delta_restore_range':[0,255],
            'largest_left_shift':10,'maximum_packed_int':262143,'all_shift_operands_nonnegative':True,
            'local_channels_written_before_each_use':True,'changes_initialized_to_three_parameter_objects_in_order':True,
            'history_inner_index_range':[0,2],'history_declared_row_stride_bytes':12,
            'external_first_dimension_extent_established':False},
        'required_unproved_conditions':machine['required_unproved_conditions']+[
            'Target C integer representation has8-bit unsigned char,16-bit short,32-bit int/unsigned int, two\u0027s-complement signed short and ordinary integer promotions.',
            'Out-of-range int-to-signed-short conversion uses low16 interpreted signed without raising a signal; this includes channels[j] compound assignment.',
            'The established entry ABI transports the six source parameter values into the listed register/entry-stack lower bits, with valid incoming stack words.',
            'Every executed external C array access is within a live suitably aligned object with the declared element/row type, permits the requested read/write, and yields a defined value; no first-dimension extent or initialization follows from a canonical symbol point.',
            'Automatic C objects and their copied pointers retain their language lifetimes/provenance and correspond to the already conditional machine frame; the external objects do not alias or asynchronously mutate that frame, code, parameters or private state.',
            'The source/object lineage association and frozen certificates are independently authenticated; this bridge does not itself admit source or ELF into a native selector.'],
        'read_value_quantification':'Distinct ordered reads are arbitrary observations. Read identifiers are freshly scoped to every dynamic iteration, with no cross-read or cross-iteration stability assumed.',
        'reused_authority':reuse_authority,'conditional_C_AST_value_access_correspondence':True,
        'physical_memory_permission':False,'source_or_ELF_admission':False,'native_admission':False,
        'compiler_executions':0,'old_producer_executions':0}
