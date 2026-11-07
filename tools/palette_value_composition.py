"""Conditional symbolic machine values with explicit ordered memory reads.

This private composition consumes independently established copy, frame,
channel-arithmetic and loop certificates. It does not supply physical memory
permissions, C source admission, or a native selector.
"""
from dataclasses import dataclass, field
import hashlib
import json

import match

SELECTOR='conditional-palette-owner-value-composition-v1'
MASK=0xffffffff
MAX_STEPS=2048


def constant(value):return ('constant',value&MASK)


def bounds(value):
    op=value[0]
    if op=='constant':return value[1],value[1]
    if op=='input':return 0,(1<<value[2])-1
    if op=='read':return 0,(1<<(8*value[2]))-1
    if op in ('low','extract'):return 0,(1<<value[-1])-1
    if op=='adjust16':return 0,max(bounds(value[1])[1],31)
    if op=='add':
        ranges=[bounds(term) for term in value[1]];low=sum(r[0] for r in ranges);high=sum(r[1] for r in ranges)
        return (low,high) if high<=MASK else (0,MASK)
    if op=='mul':
        low,high=bounds(value[2]);return (value[1]*low,value[1]*high) if value[1]*high<=MASK else (0,MASK)
    if op=='and':return 0,value[2]
    if op=='lsr':
        low,high=bounds(value[1]);return low>>value[2],high>>value[2]
    if op=='or':return 0,(1<<max(bounds(term)[1].bit_length() for term in value[1]))-1
    if op in ('opaque','lsl','sext16'):return 0,MASK
    raise ValueError('value is not an architectural scalar')


def add(*values):
    stacks=[value for value in values if value[0]=='stack']
    if stacks:
        rest=[value for value in values if value[0]!='stack']
        if len(stacks)!=1 or any(value[0]!='constant' for value in rest):
            raise ValueError('local pointer addition needs an exact scalar offset')
        return ('stack',stacks[0][1]+sum(value[1] if value[1]<(1<<31) else value[1]-(1<<32) for value in rest))
    terms=[]
    for value in values:
        bounds(value);terms.extend(value[1] if value[0]=='add' else (value,))
    total=0;coefficients={}
    for value in terms:
        if value[0]=='constant':total+=value[1]
        else:
            coefficient,term=(value[1],value[2]) if value[0]=='mul' else (1,value)
            coefficients[term]=(coefficients.get(term,0)+coefficient)&MASK
    result=[multiply(coefficient,term) for term,coefficient in coefficients.items() if coefficient]
    if total&MASK:result.append(constant(total))
    if not result:return constant(0)
    return result[0] if len(result)==1 else ('add',tuple(sorted(result,key=repr)))


def multiply(coefficient,value):
    bounds(value);coefficient&=MASK
    if not coefficient:return constant(0)
    if coefficient==1:return value
    if value[0]=='constant':return constant(coefficient*value[1])
    if value[0]=='mul':return multiply(coefficient*value[1],value[2])
    if value[0]=='add':return add(*(multiply(coefficient,term) for term in value[1]))
    return ('mul',coefficient,value)


def low(value,width):
    if not 1<=width<=32:raise ValueError('invalid scalar narrowing width')
    if value[0]=='constant':return constant(value[1]&((1<<width)-1))
    if bounds(value)[1]<(1<<width):return value
    if value[0]=='low':return low(value[1],min(width,value[2]))
    return ('low',value,width)


def left(value,amount):
    bounds(value)
    if not 0<=amount<=31:raise ValueError('invalid left shift')
    if value[0]=='constant':return constant(value[1]<<amount)
    return ('lsl',value,amount) if amount>=16 else multiply(1<<amount,value)


def right(value,amount):
    bounds(value)
    if not 1<=amount<=32:raise ValueError('invalid unsigned right shift')
    if value[0]=='constant':return constant(value[1]>>amount)
    if value[0]=='lsl' and value[2]==amount:return low(value[1],32-amount)
    if value[0]=='mul' and value[1]==1<<amount:return low(value[2],32-amount)
    if value[0]=='and' and value[2]%(1<<amount)==0:
        mask=value[2]>>amount
        if mask and mask&(mask+1)==0:return ('extract',value[1],amount,mask.bit_length())
    return ('lsr',value,amount)


def band(value,mask):
    bounds(value)
    if type(mask) is not int or not 0<=mask<=MASK:raise ValueError('AND lacks exact architectural mask')
    if value[0]=='constant':return constant(value[1]&mask)
    if not mask:return constant(0)
    if mask&(mask+1)==0:return low(value,mask.bit_length())
    return ('and',value,mask)


def bor(*values):
    terms=[];fixed=0
    for value in values:
        bounds(value)
        for term in value[1] if value[0]=='or' else (value,):
            if term[0]=='constant':fixed|=term[1]
            else:terms.append(term)
    if fixed:terms.append(constant(fixed))
    terms=sorted(set(terms),key=repr)
    if not terms:return constant(0)
    return terms[0] if len(terms)==1 else ('or',tuple(terms))


def adjust(channel,delta):
    channel,delta=low(channel,16),low(delta,16)
    if delta==constant(0):return channel
    if channel[0]==delta[0]=='constant':
        total=(channel[1]+delta[1])&65535;total=total if total<32768 else total-65536
        return constant(min(max(total,0),31))
    return ('adjust16',channel,delta)


def evaluate(value,inputs,reads=()):
    op=value[0]
    if op=='constant':return value[1]
    if op=='input':return inputs[value[1]]&((1<<value[2])-1)
    if op=='read':return reads[value[1]]&((1<<(8*value[2]))-1)
    if op=='add':return sum(evaluate(term,inputs,reads) for term in value[1])&MASK
    if op=='mul':return value[1]*evaluate(value[2],inputs,reads)&MASK
    if op=='low':return evaluate(value[1],inputs,reads)&((1<<value[2])-1)
    if op=='extract':return (evaluate(value[1],inputs,reads)>>value[2])&((1<<value[3])-1)
    if op=='and':return evaluate(value[1],inputs,reads)&value[2]
    if op=='or':
        result=0
        for term in value[1]:result|=evaluate(term,inputs,reads)
        return result
    if op=='lsl':return evaluate(value[1],inputs,reads)<<value[2]&MASK
    if op=='lsr':return evaluate(value[1],inputs,reads)>>value[2]
    if op=='sext16':
        result=evaluate(value[1],inputs,reads)&65535
        return (result if result<32768 else result-65536)&MASK
    if op=='adjust16':
        channel=evaluate(value[1],inputs,reads)&65535;delta=evaluate(value[2],inputs,reads)&65535
        if not delta:return channel
        total=(channel+delta)&65535;total=total if total<32768 else total-65536
        return min(max(total,0),31)
    raise ValueError('cannot evaluate pointer or opaque saved value')


@dataclass
class State:
    registers:dict
    memory:dict
    sp:int=0
    protected:set=field(default_factory=set)
    comparison:object=None
    guards:tuple=()
    events:tuple=()
    trace:tuple=()
    macros:tuple=()

    def clone(self):
        return State(dict(self.registers),dict(self.memory),self.sp,set(self.protected),self.comparison,
                     self.guards,self.events,self.trace,self.macros)

    def value(self,register):
        if register==13:return ('stack',self.sp)
        value=self.registers.get(register)
        if value is None:raise ValueError('value trace reads a register without a justified value')
        return value

    def load_local(self,offset,width):
        if width not in (1,2,4) or offset%width or (offset,width) not in self.memory:
            raise ValueError('value trace reads uninitialized or mismatched local bytes')
        return self.memory[offset,width]

    def store_local(self,offset,width,value,*,save=False):
        if width not in (1,2,4) or offset%width or not self.sp<=offset or offset+width>0 or any(
                byte in self.protected for byte in range(offset,offset+width)):
            raise ValueError('value trace writes outside local allocation or into protected saves')
        if value[0]=='stack' and width!=4:raise ValueError('value trace truncates a local pointer')
        for start,size in tuple(self.memory):
            if start<offset+width and offset<start+size:del self.memory[start,size]
        self.memory[offset,width]=value if value[0]=='stack' else low(value,8*width)
        if save:self.protected.update(range(offset,offset+width))


class Machine:
    def __init__(self,data,address,sites,literals,external_records,copy_observation=None,arithmetic_regions=()):
        self.data=data;self.address=address;self.instructions={};self.literals=literals
        self.external_records=external_records;self.copy_observation=copy_observation
        self.arithmetic_regions={row['entry']:row for row in arithmetic_regions}
        decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        for site in sites:
            if type(site) is not int or site&1 or not address<=site<address+len(data):
                raise ValueError('value instruction leaves retained owner')
            items=list(decoder.disasm(data[site-address:site-address+4],site,count=1))
            if len(items)!=1:raise ValueError('value instruction cannot be decoded')
            self.instructions[site]=items[0]

    def external(self,state,site,address,width,writing,value=None):
        lo,hi=bounds(address);kind='external-write' if writing else 'external-read'
        if not any(row[0]==kind and row[1]==site and row[4]==width and row[2]<=lo and hi+width<=row[3] for row in self.external_records):
            raise ValueError('value external address leaves retained numerical footprint')
        if writing:
            if value[0]=='stack':raise ValueError('value trace exports a local pointer')
            value=low(value,8*width)
        else:value=('read',len(state.events),width,address)
        state.events+=((kind,site,address,width,value),)
        return value

    def copy(self,state,site):
        row=self.copy_observation
        if row is None or row['site']!=site or row['consumer_sha256']!=hashlib.sha256(self.data).hexdigest():
            raise ValueError('value trace lacks authenticated copy call')
        item=self.instructions[site]
        if item.mnemonic!='bl' or item.operands[0].imm!=row['address'] or state.value(0)!=('stack',row['destination']) or \
                state.value(1)!=('stack',row['source']) or state.value(2)!=constant(row['count']):
            raise ValueError('value copy call differs from retained actual arguments')
        if row['count']%4 or row['preserved_registers']!=list(range(4,13)) or row['SP_restored'] is not True or \
                row['returned_local_aliases']!=[[0,row['destination']],[3,row['source']+row['count']]]:
            raise ValueError('value copy effects differ from required retained contract')
        if row['transfers']!=[[row['source']+i,row['destination']+i] for i in range(row['count'])]:
            raise ValueError('value copy byte transfers are not complete')
        if row['count']<=0 or max(row['source'],row['destination'])<min(row['source'],row['destination'])+row['count']:
            raise ValueError('value copy spans must be positive and disjoint')
        values=[state.load_local(row['source']+offset,4) for offset in range(0,row['count'],4)]
        if any(value[0]!='stack' for value in values):raise ValueError('value copy source is not initialized local pointer words')
        for offset,value in zip(range(0,row['count'],4),values):state.store_local(row['destination']+offset,4,value)
        state.registers.update({0:('stack',row['destination']),1:None,2:None,3:('stack',row['source']+row['count']),14:None})
        state.comparison=None;state.macros+=((site,'retained-pointer-copy'),)
        return site+item.size,state

    def arithmetic(self,state,site):
        proof=self.arithmetic_regions[site];roles={}
        for register,binding in proof['entry_bindings']:
            if binding in ('channel_pointer','adjustment_pointer'):
                value=state.value(register)
                if value[0]!='stack' or value[1] not in proof['authenticated_entry_evidence']['local_role_offsets'][binding]:
                    raise ValueError('value arithmetic local pointer differs from retained role')
                roles[binding]=value[1]
            elif type(binding) is int and state.value(register)!=constant(binding):
                raise ValueError('value arithmetic constant input differs')
        channel=state.load_local(roles['channel_pointer'],2);delta=state.load_local(roles['adjustment_pointer'],2)
        for register,binding in proof['entry_bindings']:
            if binding=='channel_value' and state.value(register)!=channel:
                raise ValueError('value arithmetic preloaded channel differs from local cell')
        state.store_local(roles['channel_pointer'],2,adjust(channel,delta))
        written=set()
        for reached in proof['reached_sites']:
            written.update(self.instructions[reached].regs_access()[1])
        for register in range(13):
            if match.ARM_REG_R0+register in written:state.registers[register]=None
        state.comparison=None;state.macros+=((site,'retained-halfword-adjustment',channel,delta),)
        return proof['exit'],state

    def step(self,site,incoming):
        if site not in self.instructions:raise ValueError('value trace leaves retained instructions')
        state=incoming.clone();state.trace+=(site,)
        if len(state.trace)>MAX_STEPS:raise ValueError('value trace exceeds bounded step budget')
        if site in self.arithmetic_regions:return [self.arithmetic(state,site)]
        item=self.instructions[site];raw=int.from_bytes(item.bytes,'little');target=site+item.size
        if item.mnemonic=='bl':return [self.copy(state,site)]
        if item.size!=2:raise ValueError('unsupported wide value instruction')
        if raw&0xf800==0xe000:return [(item.operands[0].imm,state)]
        if raw&0xf000==0xd000:
            condition=(raw>>8)&15
            if condition not in (0,1,8,9) or state.comparison is None:raise ValueError('value branch lacks supported exact comparison')
            left_value,right_value=state.comparison
            yes,no={0:('eq','ne'),1:('ne','eq'),8:('ugt','ule'),9:('ule','ugt')}[condition]
            if left_value[0]==right_value[0]=='constant':
                a,b=left_value[1],right_value[1];truth={'eq':a==b,'ne':a!=b,'ugt':a>b,'ule':a<=b}[yes]
                return [(item.operands[0].imm if truth else target,state)]
            result=[]
            for destination,relation in ((item.operands[0].imm,yes),(target,no)):
                branch=state.clone();branch.guards+=((relation,left_value,right_value),);result.append((destination,branch))
            return result
        if raw&0xfe00==0xb400:
            registers=[r for r in range(8) if raw&(1<<r)]+([14] if raw&0x100 else [])
            if not registers:raise ValueError('empty value push')
            state.sp-=4*len(registers)
            for i,register in enumerate(registers):state.store_local(state.sp+4*i,4,state.value(register),save=True)
        elif raw&0xff00==0xb000:
            delta=(raw&127)*4;state.sp+=-delta if raw&128 else delta
        elif raw&0xf800==0xa800:state.registers[(raw>>8)&7]=('stack',state.sp+(raw&255)*4)
        elif raw&0xff00==0x4600:
            destination,source=(raw&7)+((raw>>4)&8),(raw>>3)&15
            if destination>12 or source>13:raise ValueError('value MOV changes control state')
            state.registers[destination]=state.value(source)
        elif item.mnemonic=='cmp':
            operands=[]
            for operand in item.operands:
                operands.append(state.value(operand.reg-match.ARM_REG_R0) if operand.type==match.ARM_OP_REG else constant(operand.imm))
            if len(operands)!=2:raise ValueError('value comparison differs')
            state.comparison=tuple(operands)
        elif raw&0xf800==0x2000:state.registers[(raw>>8)&7]=constant(raw&255);state.comparison=None
        elif raw&0xfc00==0x1c00:
            delta=(raw>>6)&7
            state.registers[raw&7]=add(state.value((raw>>3)&7),constant(-delta if raw&0x200 else delta));state.comparison=None
        elif raw&0xfe00==0x1800:
            state.registers[raw&7]=add(state.value((raw>>3)&7),state.value((raw>>6)&7));state.comparison=None
        elif raw&0xf000==0x3000:
            register=(raw>>8)&7;state.registers[register]=add(state.value(register),constant(-(raw&255) if raw&0x800 else raw&255));state.comparison=None
        elif raw&0xff00==0x4400:
            destination,source=(raw&7)+((raw>>4)&8),(raw>>3)&15
            if destination>12 or source>13:raise ValueError('value ADD changes control state')
            state.registers[destination]=add(state.value(destination),state.value(source))
        elif raw&0xf800 in (0x0000,0x0800):
            amount=(raw>>6)&31;value=state.value((raw>>3)&7)
            state.registers[raw&7]=left(value,amount) if raw&0xf800==0 else right(value,amount or 32);state.comparison=None
        elif raw&0xffc0 in (0x4000,0x4300):
            destination,source=raw&7,(raw>>3)&7
            a,b=state.value(destination),state.value(source)
            if raw&0xffc0==0x4300:state.registers[destination]=bor(a,b)
            elif a[0]=='constant':state.registers[destination]=band(b,a[1])
            elif b[0]=='constant':state.registers[destination]=band(a,b[1])
            else:raise ValueError('value AND lacks exact mask')
            state.comparison=None
        elif item.mnemonic in ('ldr','ldrh','ldrb','str','strh','strb'):
            register=item.operands[0].reg-match.ARM_REG_R0;mem=item.operands[1].mem
            width={'ldr':4,'str':4,'ldrh':2,'strh':2,'ldrb':1,'strb':1}[item.mnemonic]
            writing=item.mnemonic.startswith('str')
            if mem.base==match.ARM_REG_PC:
                literal=((site+4)&~3)+mem.disp
                if writing or width!=4 or mem.index or literal not in self.literals:raise ValueError('value literal differs from retained partition')
                state.registers[register]=constant(self.literals[literal])
            else:
                base=13 if mem.base==match.ARM_REG_SP else mem.base-match.ARM_REG_R0
                address=add(state.value(base),constant(mem.disp),*( [state.value(mem.index-match.ARM_REG_R0)] if mem.index else []))
                if address[0]=='stack':
                    if writing:state.store_local(address[1],width,state.value(register))
                    else:state.registers[register]=state.load_local(address[1],width)
                elif writing:self.external(state,site,address,width,True,state.value(register))
                else:state.registers[register]=self.external(state,site,address,width,False)
        else:raise ValueError('unsupported value instruction: '+item.mnemonic)
        return [(target,state)]

    def run(self,start,state,stops):
        pending=[(start,state)];finished=[]
        while pending:
            site,current=pending.pop()
            if site in stops:finished.append((site,current));continue
            pending.extend(self.step(site,current))
            if len(pending)+len(finished)>64:raise ValueError('value trace path budget exceeded')
        return finished


def certificate_digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def initial_state():
    registers={r:('input',f'r{r}',32) if r<4 else ('opaque',f'entry-r{r}') for r in range(13)}
    registers[14]=('opaque','entry-return')
    return State(registers,{(0,4):('input','incoming0',32),(4,4):('input','incoming4',32)})


def reference_values():
    first=low(('input','r0',32),16);count=low(('input','r1',32),16)
    deltas=[low(('input','r2',32),16),low(('input','r3',32),16),low(('input','incoming0',32),16)]
    restore=low(('input','incoming4',32),8)
    last=low(add(first,count,constant(-1)),16)
    return first,count,deltas,restore,last


def pack_channels(channels):
    return low(bor(channels[0],left(channels[1],5),left(channels[2],10)),16)


def prefix_contract(machine,frame,copy_observation,outer_by_mode,palette_base):
    releases=[site for site,item in machine.instructions.items()
              if match.thumb_stack_adjustment(item) is not None and match.thumb_stack_adjustment(item)>0]
    if len(releases)!=1:raise ValueError('value owner lacks unique retained frame-release entry')
    release=releases[0];headers={mode:row['header'] for mode,row in outer_by_mode.items()}
    finished=machine.run(frame['address'],initial_state(),set(headers.values())|{release})
    first,count,deltas,restore,last=reference_values()
    expected=set();observed=set();seeds={mode:[] for mode in headers};paths=[]
    channel_offsets=sorted(next(iter(machine.arithmetic_regions.values()))['authenticated_entry_evidence']['local_role_offsets']['channel_pointer'])
    adjustment_offsets=sorted(next(iter(machine.arithmetic_regions.values()))['authenticated_entry_evidence']['local_role_offsets']['adjustment_pointer'])
    if len(channel_offsets)!=3 or len(adjustment_offsets)!=3 or any(b-a!=2 for a,b in zip(channel_offsets,channel_offsets[1:])):
        raise ValueError('value owner does not have three adjacent local channel cells')
    for limited,limit in ((False,last),(True,constant(511))):
        minimum=('ugt' if limited else 'ule',last,constant(511))
        for mode in ('normal','restore'):
            selected=('eq' if mode=='normal' else 'ne',restore,constant(0))
            for entered in (False,True):
                guard=('ule' if entered else 'ugt',first,limit)
                expected.add((frozenset((minimum,selected,guard)),headers[mode] if entered else release,limit))
    for site,state in finished:
        key=frozenset(state.guards),site,state.value(8)
        observed.add(key)
        if state.events or state.sp!=channel_offsets[0] or state.value(4)!=first:
            raise ValueError('value entry path has unexpected effects, frame or initial counter')
        if [state.load_local(offset,2) for offset in adjustment_offsets]!=deltas:
            raise ValueError('value entry adjustment cells differ from incoming lower halfwords')
        for i,offset in enumerate(adjustment_offsets):
            if state.load_local(copy_observation['source']+4*i,4)!=('stack',offset) or \
                    state.load_local(copy_observation['destination']+4*i,4)!=('stack',offset):
                raise ValueError('value entry copied pointer table has wrong channel order')
        for mode,header in headers.items():
            if site!=header:continue
            if mode=='normal':
                required={6:('stack',channel_offsets[0]),9:constant(palette_base),10:('stack',copy_observation['destination'])}
            else:required={9:('stack',copy_observation['destination']),10:constant(0)}
            if any(state.value(register)!=value for register,value in required.items()):
                raise ValueError('value entry invariant registers differ from branch contract')
            seeds[mode].append(state)
        paths.append({'stop':site,'guards':state.guards,'last':state.value(8),'trace':state.trace,'macros':state.macros})
    if len(finished)!=8 or observed!=expected or any(len(rows)!=2 for rows in seeds.values()):
        raise ValueError('value entry cases differ from wrapped min/restore/inclusive guard')
    # Both paths through the minimum differ only in R8 and their guard facts.
    for mode,rows in seeds.items():
        if rows[0].memory!=rows[1].memory or rows[0].sp!=rows[1].sp or rows[0].protected!=rows[1].protected or \
                {r:v for r,v in rows[0].registers.items() if r!=8}!={r:v for r,v in rows[1].registers.items() if r!=8}:
            raise ValueError('value minimum branches have additional uncomposed state differences')
    return seeds,paths,release,channel_offsets,adjustment_offsets


def iteration_contract(machine,mode,seed,outer,channels,deltas,palette_base,history_base):
    state=seed.clone();index=('input','index',9);limit=('input','limit',9)
    required={4:index,8:limit,9:seed.value(9),10:seed.value(10)}
    if mode=='normal':required[6]=seed.value(6)
    state.registers={r:required.get(r) for r in range(15)}
    for offset in channels:state.memory.pop((offset,2),None)
    state.comparison=None;state.guards=();state.events=();state.trace=();state.macros=()
    original_memory=dict(state.memory)
    stop=outer['tail'][-1]
    outputs=machine.run(outer['header'],state,{stop})
    if len(outputs)!=1:raise ValueError('value iteration retains uncomposed dynamic control')
    _,result=outputs[0]
    if result.guards or len(result.macros)!=3 or any(row[1]!='retained-halfword-adjustment' for row in result.macros):
        raise ValueError('value iteration differs from exactly three closed channel adjustments')
    palette_address=add(constant(palette_base),multiply(2,index))
    history_addresses=[add(constant(history_base),multiply(12,index),constant(j)) for j in range(3)]
    events=result.events
    if len(events)!=(7 if mode=='normal' else 4):raise ValueError('value iteration has unexpected external effect count')
    read_values=[]
    for j,event in enumerate(events[:3]):
        kind,site,address,width,value=event
        expected_address=palette_address if mode=='normal' else history_addresses[j]
        if kind!='external-read' or address!=expected_address or width!=(2 if mode=='normal' else 1) or value!=('read',j,width,address):
            raise ValueError('value input read order/address/width differs')
        read_values.append(value)
    if mode=='normal':
        extracted=[low(read_values[0],5),('extract',read_values[1],5,5),('extract',read_values[2],10,5)]
        for j,event in enumerate(events[3:6]):
            kind,_,address,width,value=event
            if (kind,address,width,value)!=('external-write',history_addresses[j],1,extracted[j]):
                raise ValueError('value history write is not the original corresponding extracted channel')
    else:extracted=read_values
    updated=[adjust(channel,delta) for channel,delta in zip(extracted,deltas)]
    kind,_,address,width,value=events[-1]
    if (kind,address,width,value)!=('external-write',palette_address,2,pack_channels(updated)):
        raise ValueError('value palette packing differs from updated corresponding channel cells')
    if [result.load_local(offset,2) for offset in channels]!=updated:
        raise ValueError('value local channel results differ from ordered input/adjustment pairing')
    if {key:value for key,value in result.memory.items() if key not in {(offset,2) for offset in channels}}!=original_memory:
        raise ValueError('value iteration changes non-channel local/incoming/saved cells')
    if result.sp!=seed.sp or result.protected!=seed.protected or result.value(4)!=add(index,constant(1)):
        raise ValueError('value iteration frame or exact next-index differs')
    for register,value in required.items():
        if register!=4 and result.value(register)!=value:raise ValueError('value iteration breaks loop invariant register')
    if result.comparison!=(add(index,constant(1)),limit):raise ValueError('value iteration ends at a different repeat comparison')
    return {'mode':mode,'header':outer['header'],'stop':stop,'index_domain':[0,511],
        'events':events,'channel_inputs':extracted,'channel_outputs':updated,
        'next_index':result.value(4),'limit':limit,'trace':result.trace,'macros':result.macros,
        'invariant_registers':sorted(required),'non_channel_memory_unchanged':True,
        'distinct_external_read_tokens_preserved':True,'history_byte_upper_bound_assumed':False,
        'packing_signed32_overflow':False,'packing_word_upper_bound':bounds(bor(updated[0],left(updated[1],5),left(updated[2],10)))[1]}


def verify(data,address,rom,certificates,*,selector,reuse_authority,palette_base,history_base):
    if selector!=SELECTOR or type(selector) is not str or type(data) is not bytes or type(rom) is not bytes:
        raise ValueError('value composition requires explicit immutable input/selector')
    required={'copy','frame','numeric','arithmetic','first_use','loops'}
    if set(certificates)!=required or type(reuse_authority) is not dict or reuse_authority.get('independently_established_frozen_certificates') is not True:
        raise ValueError('value composition requires all independent retained certificates')
    for name,value in certificates.items():
        if reuse_authority.get(name+'_sha256')!=certificate_digest(value):raise ValueError('value retained certificate digest differs')
    copy=certificates['copy'];frame=certificates['frame'];numeric=certificates['numeric'];loops=certificates['loops']
    body_sha=hashlib.sha256(data).hexdigest();rom_sha=hashlib.sha256(rom).hexdigest()
    if not 0x08000000<=address or rom[address-0x08000000:address-0x08000000+len(data)]!=data:
        raise ValueError('value owner differs from complete current ROM')
    for context in (copy['prefix'],frame,numeric,loops):
        if context['address']!=address or context['end']!=address+len(data) or context['body_sha256']!=body_sha or context['ROM_sha256']!=rom_sha:
            raise ValueError('value retained context differs from exact owner/ROM')
    if frame['partition']!=numeric['partition'] or frame['partition']!=copy['prefix']['partition']:
        raise ValueError('value retained complete partitions differ')
    arithmetic=certificates['arithmetic'];first_use=certificates['first_use']
    if arithmetic['status']!='PASS_CONDITIONAL_SIGNED_HALFWORD_ARITHMETIC_BOTH_REGIONS' or \
            first_use['status']!='PASS_NEW_FIRST_USE_GUARD_ON_FROZEN_ARITHMETIC_PATHS' or \
            first_use['actual_arithmetic_capture']['sha256']!=reuse_authority.get('arithmetic_file_sha256') or \
            not first_use['arithmetic_functions_AST_unchanged'] or not first_use['composer_AST_diff_only_new_guard_and_evidence']:
        raise ValueError('value arithmetic/first-use composition is not independently closed')
    region_by_mode={row['name']:row['receipt'] for row in arithmetic['regions']}
    if set(region_by_mode)!={'normal','restore'}:raise ValueError('value arithmetic branch contracts differ')
    for mode,region in region_by_mode.items():
        if region['body_sha256']!=body_sha or region['owner_address']!=address or region['owner_end']!=address+len(data):
            raise ValueError('value arithmetic region belongs to another owner')
        if not any(row['name']==mode and all(item['earlier_reads_or_writes'] is False for item in row['pointer_first_uses']) for row in first_use['regions']):
            raise ValueError('value arithmetic entry pointers lack retained first-use guard')
    observations=copy['copy']['observations']
    if len(observations)!=1 or observations[0]['count']!=12:raise ValueError('value initializer is not sole exact12-byte pointer copy')
    observation=observations[0];helper=observation['address']-0x08000000
    if hashlib.sha256(rom[helper:helper+copy['copy']['canonical_bytes']]).hexdigest()!=copy['copy']['canonical_sha256']:
        raise ValueError('value retained initializer body differs from ROM')
    if len(loops['inner_loops'])!=2 or len(loops['outer_loops'])!=2 or any(row['iterations']!=3 for row in loops['inner_loops']):
        raise ValueError('value composition lacks two exact three-channel loops')
    outer_by_mode={}
    for mode,region in region_by_mode.items():
        owners=[row for row in loops['outer_loops'] if region['entry'] in row['nodes']]
        if len(owners)!=1:raise ValueError('value arithmetic has no unique containing outer loop')
        outer=owners[0]
        if (outer['counter'],outer['limit_register'],outer['carry_register'],outer['maximum_iterations'])!=(4,8,12,512):
            raise ValueError('value loop induction contract differs')
        outer_by_mode[mode]=outer
    sites={row['site'] for row in numeric['fixed_point_states']}
    literals={row['address']:row['value'] for row in frame['partition']['words']}
    machine=Machine(data,address,sites,literals,frame['continuation']['records'],observation,region_by_mode.values())
    seeds,prefix,release,channels,adjustment_offsets=prefix_contract(machine,frame,observation,outer_by_mode,palette_base)
    deltas=reference_values()[2]
    iterations=[iteration_contract(machine,mode,seeds[mode][0],outer_by_mode[mode],channels,deltas,palette_base,history_base) for mode in ('normal','restore')]
    epilogue=[];site=release
    while True:
        if site in epilogue or site not in machine.instructions:raise ValueError('value retained epilogue is not straight')
        epilogue.append(site);item=machine.instructions[site]
        if item.mnemonic=='bx':break
        if item.mnemonic not in ('add','pop','mov'):raise ValueError('value epilogue has an uncomposed operation')
        site+=item.size
    if site not in frame['continuation']['restored_return_sites']:raise ValueError('value epilogue is not a retained restored return')
    coverage={site for row in prefix for site in row['trace']}|{site for row in iterations for site in row['trace']}|set(epilogue)
    coverage.update(site for region in region_by_mode.values() for site in region['reached_sites'])
    # The normal branch's final B to the common epilogue is outside one-iteration
    # value execution; it is an exact one-instruction control connector.
    connectors=[]
    for outer in outer_by_mode.values():
        site=outer['exit']
        while site!=release:
            if site in connectors or site not in machine.instructions:raise ValueError('value loop exit connector cycles')
            item=machine.instructions[site]
            if item.mnemonic!='b':raise ValueError('value loop exit has uncomposed effects')
            connectors.append(site);coverage.add(site);site=item.operands[0].imm
        coverage.add(outer['tail'][-1])
    if coverage!=sites:raise ValueError('value composition does not cover complete owner instruction set')
    return {'schema':SELECTOR,'address':address,'end':address+len(data),'body_sha256':body_sha,'ROM_sha256':rom_sha,
        'instructions':len(sites),'complete_instruction_coverage':sorted(coverage),'prefix_paths':prefix,
        'iterations':iterations,'epilogue_from_retained_frame':epilogue,'pure_exit_connectors':connectors,
        'entry_last':'min((low16(entryR0)+low16(entryR1)-1)&65535,511)',
        'restore_selector':'low8(incoming_word_at_entry_SP+4)',
        'adjustments':'low16(entryR2), low16(entryR3), low16(incoming_word_at_entry_SP)',
        'loop_composition':'Frozen055 supplies finite guarded repetition; each current value iteration preserves the next iteration invariants and exact successor.',
        'required_unproved_conditions':frame['required_unproved_conditions']+loops['required_unproved_conditions'][-1:]+[
            'For C interpretation, retain054 target low16 signed-short conversion condition. Original C parsing and source/native admission remain separate.'],
        'reused_certificate_authority':reuse_authority,'old_producer_executions':0,
        'conditional_owner_machine_value_trace':True,'unconditional_termination':False,
        'physical_memory_permission':False,'source_or_ELF_admission':False,'native_admission':False}
