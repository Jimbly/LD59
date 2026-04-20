import assert from 'assert';

let wd = (window as {
  WavedashJS?: {
    updateLoadProgressZeroToOne(v: number): void;
    init(p: { debug: boolean }): void;
    getUserId(): string;
    getUsername(): string;
  };
}).WavedashJS || null;

export function wavedashLoadProgress(value: number): void {
  wd?.updateLoadProgressZeroToOne(value);
}

let ready_called = false;
export function wavedashReady(): void {
  ready_called = true;
  wd?.init({ debug: false });
}

export function wavedashUserName(): string | null {
  assert(ready_called);
  return wd?.getUsername() || null;
}
