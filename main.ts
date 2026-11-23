// Tiny stack virtual machine: a spec-exact interpreter for make.fun's tiny stack ISA.
// Reads every instance under MAKEFUN_INPUT_DIR, executes its program.bin against
// input.bin, and writes stdout.bin plus exit.txt under MAKEFUN_OUTPUT_DIR.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";

// Per-opcode metadata: immediate length, values popped, values pushed.
// A length of -1 marks a byte that is not an opcode at all.
const IMM = new Int8Array(256).fill(-1);
const POP = new Int8Array(256);
const PSH = new Int8Array(256);
function def(op: number, imm: number, pops: number, pushes: number): void {
  IMM[op] = imm;
  POP[op] = pops;
  PSH[op] = pushes;
}
def(0x00, 0, 0, 0); // HALT
def(0x01, 1, 0, 1); // PUSH8
def(0x02, 4, 0, 1); // PUSH32
def(0x03, 0, 1, 0); // POP
def(0x04, 0, 1, 2); // DUP
def(0x05, 0, 2, 2); // SWAP
def(0x06, 0, 2, 3); // OVER
def(0x07, 0, 3, 3); // ROT
for (const op of [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]) def(op, 0, 2, 1);
def(0x17, 0, 1, 1); // NEG
def(0x1b, 0, 1, 1); // NOT
def(0x30, 2, 0, 0); // JMP
def(0x31, 2, 1, 0); // JZ
def(0x32, 2, 1, 0); // JNZ
def(0x33, 2, 0, 0); // CALL
def(0x34, 0, 0, 0); // RET
def(0x40, 0, 1, 1); // LOAD
def(0x41, 0, 2, 0); // STORE
def(0x50, 0, 1, 0); // PRINT
def(0x51, 0, 1, 0); // PUTC
def(0x52, 0, 0, 1); // IN
def(0x53, 0, 1, 0); // EXIT

const STACK_CAP = 256;
const CALL_CAP = 64;
const MEM_WORDS = 256;
const STEP_CAP = 1_000_000;
const OUT_CAP = 65_536;

// Executes one program and reports the bytes it emitted and its exit code.
function execute(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const stack = new Int32Array(STACK_CAP);
  let sp = 0;
  const calls = new Int32Array(CALL_CAP);
  let csp = 0;
  const mem = new Int32Array(MEM_WORDS);
  const buf = new Uint8Array(OUT_CAP);
  let used = 0;
  let inAt = 0;
  let pc = 0;
  let steps = 0;
  const finish = (code: number) => ({ out: buf.slice(0, used), code });

  for (;;) {
    if (steps === STEP_CAP) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm < 0) return finish(5);
    if (pc + imm >= n) return finish(9);
    steps += 1;
    const next = pc + 1 + imm;
    if (sp < POP[op]) return finish(2);
    if (sp - POP[op] + PSH[op] > STACK_CAP) return finish(3);
    pc = next;

    switch (op) {
      case 0x00:
        return finish(0);
      case 0x01:
        stack[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02:
        stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp -= 1;
        break;
      case 0x04:
        stack[sp] = stack[sp - 1];
        sp += 1;
        break;
      case 0x05: {
        const top = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = top;
        break;
      }
      case 0x06:
        stack[sp] = stack[sp - 2];
        sp += 1;
        break;
      case 0x07: {
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = a;
        break;
      }
      case 0x17:
        stack[sp - 1] = -stack[sp - 1] | 0;
        break;
      case 0x1b:
        stack[sp - 1] = ~stack[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1];
        const a = stack[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return finish(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return finish(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return finish(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return finish(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        stack[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let go = true;
        if (op !== 0x30) {
          const v = stack[--sp];
          go = op === 0x31 ? v === 0 : v !== 0;
        }
        if (go) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === CALL_CAP) return finish(7);
        calls[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return finish(8);
        pc = calls[--csp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return finish(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return finish(6);
        mem[addr] = stack[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const text = String(stack[sp - 1]);
        if (used + text.length > OUT_CAP) return finish(11);
        sp -= 1;
        for (let i = 0; i < text.length; i++) buf[used++] = text.charCodeAt(i);
        break;
      }
      case 0x51:
        if (used + 1 > OUT_CAP) return finish(11);
        buf[used++] = stack[--sp] & 255;
        break;
      case 0x52:
        stack[sp++] = inAt < input.length ? input[inAt++] : -1;
        break;
      case 0x53:
        return finish(stack[--sp] & 255);
    }
  }
}

const ids = readdirSync(IN_DIR, { withFileTypes: true })
  .filter((e) => e.isDirectory())
  .map((e) => e.name)
  .sort();
for (const id of ids) {
  const prog = readFileSync(join(IN_DIR, id, "program.bin"));
  const input = readFileSync(join(IN_DIR, id, "input.bin"));
  const { out, code } = execute(prog, input);
  const dir = join(OUT_DIR, id);
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, "stdout.bin"), out);
  writeFileSync(join(dir, "exit.txt"), `${code}\n`);
}
