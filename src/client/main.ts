/* eslint n/global-require:off */
// eslint-disable-next-line import/order
const local_storage = require('glov/client/local_storage');
local_storage.setStoragePrefix('ld59'); // Before requiring anything else that might load from this

import assert from 'assert';
import { autoAtlas } from 'glov/client/autoatlas';
import * as camera2d from 'glov/client/camera2d';
import { platformParameterGet } from 'glov/client/client_config';
import * as engine from 'glov/client/engine';
import { ALIGN, Font, fontStyle, fontStyleColored } from 'glov/client/font';
import { drag, KEYS, mousePos, mouseUpEdge } from 'glov/client/input';
import { netInit } from 'glov/client/net';
import { spriteSetGet } from 'glov/client/sprite_sets';
import {
  button,
  playUISound,
  scaleSizes,
  setButtonHeight,
  setFontHeight,
  setFontStyles,
  uiGetFont,
} from 'glov/client/ui';
import { randCreate } from 'glov/common/rand_alea';
import { clamp, easeIn, easeInOut, lerp, ridx } from 'glov/common/util';
import { JSVec2, JSVec4, v4copy, v4lerp, Vec4, vec4 } from 'glov/common/vmath';
import { PAL_BLACK, PAL_BORDER, PAL_WHITE, palette, palette_font } from './palette';

const { abs, floor, max, min } = Math;

window.Z = window.Z || {};
Z.BACKGROUND = 1;
Z.SPRITES = 10;
Z.MAP = 10;
Z.FLOATERS = 20;

// Virtual viewport for our game logic
const game_width = 384;
const game_height = 256;

const TILE_SIZE = 15;
const FONT_HEIGHT = 8;
const BUTTON_HEIGHT = TILE_SIZE + 4;

let font: Font;

function init(): void {
  // anything?
  autoAtlas('main', 'base');
}

const clear_color = palette[PAL_BORDER];

const style_floater = fontStyle(null, {
  color: palette_font[PAL_WHITE],
  outline_width: 2.5,
  outline_color: palette_font[PAL_BLACK],
});

const SIGNAL_DIST = 5;

// eslint-disable-next-line @typescript-eslint/no-unused-vars
const RESOURCES = [
  'wood',
  'stone',
  'fruit',
  'beer',
  'jam',
  'fire',
] as const;
type ResourceType = typeof RESOURCES[number];
const BASE_RESOURCES = [
  'wood',
  'stone',
  'fruit'
] as const;
type BaseResourceType = typeof BASE_RESOURCES[number];
type LevelDef = {
  w: number;
  h: number;
  starting_power: number;
  starting_money: number;
  resources: Record<BaseResourceType, number>;
  seed: number;
};

const level_defs: LevelDef[] = [{
  w: 11,
  h: 11,
  starting_power: 7,
  starting_money: 600,
  seed: 1234,
  resources: {
    wood: 3,
    stone: 3,
    fruit: 3,
  },
}, ...(engine.DEBUG ? [{
  w: 11,
  h: 11,
  starting_power: 7,
  starting_money: 5000,
  seed: 1234,
  resources: {
    wood: 3,
    stone: 3,
    fruit: 3,
  },
}] : [])];

type FloatStyle = 'base_sale' | 'error' | 'buy' | 'sell';
const FLOAT_TIME: Record<FloatStyle, number> = {
  base_sale: 3000,
  error: 1000,
  buy: 1000,
  sell: 1000,
};

const ROT_TO_DIR = [
  'up',
  'right',
  'down',
  'left',
] as const;
const DX = [0, 1, 0, -1];
const DY = [-1, 0, 1, 0];

type CellType = 'base' | 'craft' | 'resource' | 'spawner' | 'rotate' | 'signal-stop' | 'signal-go' | 'storage';
const TILE_TYPE_SIZE: Partial<Record<CellType, number>> = {
  base: 3,
  craft: 2,
};
const MAX_ROT: Partial<Record<CellType, number>> = {
  craft: 4,
  spawner: 4,
  rotate: 2,
};
const BLOCKING_TYPE: Partial<Record<CellType, true>> = {
  base: true,
  craft: true,
  resource: true,
  storage: true,
};
type MapEntry = {
  type: CellType;
  resource?: ResourceType;
  nodraw?: boolean;
  rot?: number;
};

type Drone = {
  last_x: number;
  last_y: number;
  x: number;
  y: number;
  last_rot: number;
  rot: number;
  last_contents: null | ResourceType;
  contents: null | ResourceType;
  tick_id: number;
  thinking: boolean;
  uid: number;
  gain_resource_tick?: number;
};

const cost_table: Partial<Record<CellType, JSVec2>> = {
  spawner: [200, 100],
  rotate: [20, 5],
  storage: [50, 10],
  craft: [1000, 500],
  'signal-stop': [20, 10],
  'signal-go': [20, 10],
};

const BASE_SIZE = 3;

let view_center: JSVec2 = [0, 0];

type SimMapEntry = {
  x: number;
  y: number;
  cell: MapEntry;
  contents: null | ResourceType;
  multi_contents: (undefined | ResourceType | null)[];
  quantity: number;
};

const TICKABLE_ORDER = ['base', 'craft', 'storage', 'resource'];
function cmpTickable(a: SimMapEntry, b: SimMapEntry): number {
  let ia = TICKABLE_ORDER.indexOf(a.cell.type);
  let ib = TICKABLE_ORDER.indexOf(a.cell.type);
  if (ia !== ib) {
    return ia - ib;
  }
  if (a.y !== b.y) {
    return a.y - b.y;
  }
  return a.x - b.x;
}

const VALF = 65;
const VALW = 80;
const VALS = 100;
const VAL2 = 100;

const recipes: [ResourceType, number, ResourceType, ResourceType | null][] = [
  ['beer', VALF + VALW + VAL2, 'fruit', 'wood'],
  ['jam', VALF + VALS + VAL2, 'fruit', 'stone'],
  ['fire', VALS + VALW + VAL2, 'stone', 'wood'],


  ['fruit', VALF, 'fruit', null],
  ['wood', VALW, 'wood', null],
  ['stone', VALS, 'stone', null],
];
const RESOURCE_VALUE = {} as Record<ResourceType, number>;
recipes.forEach(function (entry) {
  RESOURCE_VALUE[entry[0]] = entry[1];
});

function resourceValue(res: ResourceType): number {
  let v = RESOURCE_VALUE[res];
  assert(v);
  return v;
}
function craftResult(inputs: ResourceType[]): ResourceType {
  if (inputs.length === 1) {
    return inputs[0];
  }
  for (let ii = 0; ii < recipes.length; ++ii) {
    let entry = recipes[ii];
    if (entry[2] === inputs[0] && entry[3] === inputs[1] ||
      entry[2] === inputs[1] && entry[3] === inputs[0]
    ) {
      return entry[0];
    }
  }
  if (engine.DEBUG) {
    assert(false);
  }
  return 'fruit';
}

const base_slurp_coords = [
  // dx, dy, destination contents index
  [-1, 0, 0],
  [0, -1, 0],
  [1, -1, 1],
  [2, -1, 2],
  [3, 0, 2],
  [3, 1, 3],
  [3, 2, 4],
  [2, 3, 4],
  [1, 3, 5],
  [0, 3, 6],
  [-1, 2, 6],
  [-1, 1, 7],
];
const base_contents_coords = [
  [0, 0],
  [1, 0],
  [2, 0],
  [2, 1],
  [2, 2],
  [1, 2],
  [0, 2],
  [0, 1],
];
const craft_map = [
  // order: UR (output), LR (input), LL (input), UL (skipped)
  'out',
  'in',
  'in',
  null,
];
const craft_slurp_coords = [
  // dx, dy, destination contents index
  [1, -1, 0],
  [2, 0, 0],
  [2, 1, 1],
  [1, 2, 1],
  [0, 2, 2],
  [-1, 1, 2],
  [-1, 0, 3],
  [0, -1, 3],
];
const craft_contents_coords = [
  [1, 0],
  [1, 1],
  [0, 1],
  [0, 0],
];

type FloatCB = (style: FloatStyle, x: number, y: number, str: string) => void;

class SimState {
  power: number;
  sim_map: (SimMapEntry | undefined)[][];
  busy: number[][];
  drone_map: (Drone | undefined)[][];
  parent: GameState;

  drones: Drone[];
  tickables: SimMapEntry[];
  last_uid = 0;
  money_earned = 0;
  transfers: [
    'spawn'|'pickup'|'from'|'within', // to drone
    ResourceType, number, number, number, number
  ][] = [];
  float: FloatCB | null;
  constructor(parent: GameState, float: FloatCB | null) {
    this.float = float;
    this.parent = parent;
    let { w, h, ld, map } = parent;
    this.power = ld.starting_power;

    this.busy = new Array(h);
    this.drone_map = new Array(h);
    this.sim_map = new Array(h);
    for (let ii = 0; ii < h; ++ii) {
      this.busy[ii] = new Array(w);
      this.drone_map[ii] = new Array(w);
      this.sim_map[ii] = new Array(h);
    }

    this.drones = [];
    let drones = this.drones;
    this.tickables = [];
    let tickables = this.tickables;

    for (let jj = 0; jj < h; ++jj) {
      let row = map[jj];
      for (let ii = 0; ii < w; ++ii) {
        let cell = row[ii];
        if (!cell) {
          continue;
        }
        if (cell.type === 'spawner') {
          let drone: Drone = {
            last_x: ii,
            last_y: jj,
            x: ii,
            y: jj,
            last_rot: cell.rot || 0,
            rot: cell.rot || 0,
            contents: null,
            last_contents: null,
            tick_id: 0,
            thinking: false,
            uid: ++this.last_uid,
          };
          drones.push(drone);
          this.drone_map[jj][ii] = drone;
        } else if (cell.type === 'base' || cell.type === 'resource' ||
          cell.type === 'storage' || cell.type === 'craft'
        ) {
          let tickable: SimMapEntry = {
            x: ii,
            y: jj,
            cell,
            contents: null,
            multi_contents: [],
            quantity: 3, // only used if resource
          };
          tickables.push(tickable);
          this.sim_map[jj][ii] = tickable;
        }
      }
    }
    tickables.sort(cmpTickable);
  }

  getDrone(x: number, y: number): Drone | null {
    if (x < 0 || y < 0 || x >= this.parent.w || y >= this.parent.h) {
      // out of bounds
      return null;
    }
    return this.drone_map[y][x] || null;
  }

  tickResource(ticker: SimMapEntry): void {
    if (!ticker.quantity || this.power <= 0) {
      return;
    }
    for (let ii = 0; ii < 4; ++ii) {
      let target_x = ticker.x + DX[ii];
      let target_y = ticker.y + DY[ii];
      let drone = this.getDrone(target_x, target_y);
      if (!drone || drone.gain_resource_tick === this.tick_id) {
        continue;
      }
      if (!drone.contents) {
        drone.contents = ticker.cell.resource!;
        this.transfers.push([
          'spawn', drone.contents,
          ticker.x, ticker.y, target_x, target_y
        ]);
        drone.gain_resource_tick = this.tick_id;
        --ticker.quantity;
        // playUISound('pickup');
        if (!ticker.quantity) {
          break;
        }
      }
    }
  }
  tickBase(ticker: SimMapEntry): void {
    // First, sell off contents
    if (ticker.multi_contents) {
      for (let ii = 0; ii < ticker.multi_contents.length; ++ii) {
        let res = ticker.multi_contents[ii];
        if (res) {
          let resource_value = resourceValue(res);
          this.money_earned += resource_value;
          ticker.multi_contents[ii] = null;

          this.transfers.push([
            'within', res,
            ticker.x + base_contents_coords[ii][0], ticker.y + base_contents_coords[ii][1],
            ticker.x + 1, ticker.y + 1,
          ]);

          this.float?.(
            'base_sale',
            ticker.x + base_contents_coords[ii][0], ticker.y + base_contents_coords[ii][1],
            `${res}: +$${resource_value}`);
          // playUISound('sell');
        }
      }
    }

    if (this.power <= 0) {
      return;
    }
    for (let jj = 0; jj < base_slurp_coords.length; ++jj) {
      let target_contents = base_slurp_coords[jj][2];
      if (ticker.multi_contents[target_contents]) {
        // already full
        continue;
      }
      let target_x = ticker.x + base_slurp_coords[jj][0];
      let target_y = ticker.y + base_slurp_coords[jj][1];
      let target_drone = this.getDrone(target_x, target_y);
      if (!target_drone || target_drone.gain_resource_tick === this.tick_id) {
        continue;
      }
      if (target_drone.contents) {
        ticker.multi_contents[target_contents] = target_drone.contents;
        this.transfers.push([
          'from', target_drone.contents,
          target_x, target_y,
          ticker.x + base_contents_coords[target_contents][0], ticker.y + base_contents_coords[target_contents][1]
        ]);
        target_drone.contents = null;
        target_drone.gain_resource_tick = this.tick_id;
        // playUISound('dropoff');
      }
    }
  }
  tickCrafter(ticker: SimMapEntry): void {
    let { cell } = ticker;
    let rot = cell.rot || 0;
    let out_pos = rot;
    // craft resource if any inputs
    let inputs: ResourceType[] = [];
    for (let ii = 0; ii < 4; ++ii) {
      let target = (ii - rot + 4) % 4;
      let role = craft_map[target];
      let content = ticker.multi_contents[target];
      if (role !== 'in' || !content) {
        continue;
      }
      inputs.push(content);
      this.transfers.push([
        'within', content,
        ticker.x + craft_contents_coords[ii][0], ticker.y + craft_contents_coords[ii][1],
        ticker.x + craft_contents_coords[out_pos][0], ticker.y + craft_contents_coords[out_pos][1],
      ]);
      ticker.multi_contents[target] = null;
    }
    if (inputs.length) {
      if (ticker.multi_contents[0]) {
        // trash it
        let trash_idx = 3;
        let trash_pos = (trash_idx - rot + 4) % 4;
        this.transfers.push([
          'within', ticker.multi_contents[0],
          ticker.x + craft_contents_coords[out_pos][0], ticker.y + craft_contents_coords[out_pos][1],
          ticker.x + craft_contents_coords[trash_pos][0], ticker.y + craft_contents_coords[trash_pos][1]
        ]);
        ticker.multi_contents[0] = null;
      }
      ticker.multi_contents[0] = craftResult(inputs);
    }

    if (this.power <= 0) {
      return;
    }

    // load/unload if available
    for (let ii = 0; ii < craft_slurp_coords.length; ++ii) {
      let target_pos = craft_slurp_coords[ii][2];
      let target_contents = (target_pos - rot + 4) % 4;
      let role = craft_map[target_contents];
      if (role === 'in' && ticker.multi_contents[target_contents] ||
        role === 'out' && !ticker.multi_contents[target_contents] ||
        !role
      ) {
        // already full or wrong role or no source
        continue;
      }
      let target_x = ticker.x + craft_slurp_coords[ii][0];
      let target_y = ticker.y + craft_slurp_coords[ii][1];
      let target_drone = this.getDrone(target_x, target_y);
      if (!target_drone || target_drone.gain_resource_tick === this.tick_id ||
        role === 'in' && !target_drone.contents ||
        role === 'out' && target_drone.contents
      ) {
        continue;
      }
      if (role === 'in') {
        assert(target_drone.contents);
        assert(!ticker.multi_contents[target_contents]);
        ticker.multi_contents[target_contents] = target_drone.contents;
        this.transfers.push([
          'from', target_drone.contents,
          target_x, target_y,
          ticker.x + craft_contents_coords[target_pos][0], ticker.y + craft_contents_coords[target_pos][1]
        ]);
        target_drone.contents = null;
        target_drone.gain_resource_tick = this.tick_id;
        // playUISound('dropoff');
      } else {
        assert(role === 'out');
        assert(!target_drone.contents);
        assert(ticker.multi_contents[target_contents]);
        target_drone.contents = ticker.multi_contents[target_contents]!;
        ticker.multi_contents[target_contents] = null;
        this.transfers.push([
          'pickup', target_drone.contents,
          ticker.x + craft_contents_coords[target_pos][0], ticker.y + craft_contents_coords[target_pos][1],
          target_x, target_y
        ]);
        target_drone.gain_resource_tick = this.tick_id;
        // playUISound('craft_pickup');
      }
    }
  }
  tickStorage(ticker: SimMapEntry): void {
    if (this.power <= 0) {
      return;
    }

    // unload if possible
    if (ticker.contents) {
      for (let ii = 0; ii < 4; ++ii) {
        let target_x = ticker.x + DX[ii];
        let target_y = ticker.y + DY[ii];
        let target_drone = this.getDrone(target_x, target_y);
        if (
          !target_drone || target_drone.contents ||
          target_drone.gain_resource_tick === this.tick_id
        ) {
          continue;
        }
        target_drone.contents = ticker.contents!;
        ticker.contents = null;
        this.transfers.push([
          'pickup', target_drone.contents,
          ticker.x, ticker.y,
          target_x, target_y
        ]);
        target_drone.gain_resource_tick = this.tick_id;
      }
    }

    // load if available
    if (!ticker.contents) {
      for (let ii = 0; ii < 4; ++ii) {
        let target_x = ticker.x + DX[ii];
        let target_y = ticker.y + DY[ii];
        let target_drone = this.getDrone(target_x, target_y);
        if (
          !target_drone || !target_drone.contents ||
          target_drone.gain_resource_tick === this.tick_id
        ) {
          continue;
        }
        ticker.contents = target_drone.contents;
        this.transfers.push([
          'from', target_drone.contents,
          target_x, target_y,
          ticker.x, ticker.y
        ]);
        target_drone.contents = null;
        target_drone.gain_resource_tick = this.tick_id;
        // playUISound('dropoff');
      }
    }
  }
  tickTickable(ticker: SimMapEntry): void {
    switch (ticker.cell.type) {
      case 'base':
        this.tickBase(ticker);
        break;
      case 'craft':
        this.tickCrafter(ticker);
        break;
      case 'resource':
        this.tickResource(ticker);
        break;
      case 'storage':
        this.tickStorage(ticker);
        break;
      default:
        assert(false);
    }
  }
  tickDroneEarly(drone: Drone): void {
    drone.last_rot = drone.rot;
    drone.last_x = drone.x;
    drone.last_y = drone.y;
    drone.last_contents = drone.contents;
    let x = drone.x + DX[drone.rot];
    let y = drone.y + DY[drone.rot];
    if (x < 0 || y < 0 || x >= this.parent.w || y >= this.parent.h) {
      // out of bounds
      return;
    }
    ++this.busy[y][x];
    let other_drone = this.drone_map[x][y];
    if (other_drone && other_drone.rot === (drone.rot + 2) % 4) {
      // can't move directly across one another's paths, block both!
      this.busy[x][y] = 99;
      this.busy[drone.x][drone.y] = 99;
    }
  }

  tryMove(drone: Drone): boolean {
    let x = drone.x + DX[drone.rot];
    let y = drone.y + DY[drone.rot];
    if (x < 0 || y < 0 || x >= this.parent.w || y >= this.parent.h) {
      return false;
    }
    if (this.busy[y][x] > 1) {
      return false;
    }
    let target_tile = this.parent.map[y][x];
    if (target_tile && BLOCKING_TYPE[target_tile.type]) {
      return false;
    }
    let other_drone = this.drone_map[y][x];
    if (other_drone && other_drone.tick_id !== this.tick_id) {
      this.tickDroneActual(other_drone);
      other_drone = this.drone_map[y][x];
    }
    if (other_drone && !other_drone.thinking) {
      // didn't move, not valid
      return false;
    }
    this.drone_map[drone.y][drone.x] = undefined;
    drone.x = x;
    drone.y = y;
    this.drone_map[drone.y][drone.x] = drone;
    return true;
  }

  tickDroneActual(drone: Drone): void {
    if (drone.tick_id === this.tick_id) {
      return;
    }
    drone.tick_id = this.tick_id;
    drone.thinking = true;
    this.tryMove(drone);
    let tile = this.parent.map[drone.y][drone.x];
    if (tile && tile.type === 'rotate') {
      drone.rot = (drone.rot + (tile.rot ? 3 : 1)) % 4;
    }
    drone.thinking = false;
  }

  tick_id = 0;
  isDay0(): boolean {
    return !this.tick_id;
  }
  tick(): void {
    ++this.tick_id;
    this.transfers.length = 0;
    for (let jj = 0; jj < this.parent.h; ++jj) {
      for (let ii = 0; ii < this.parent.w; ++ii) {
        this.busy[jj][ii] = 0;
      }
    }
    for (let ii = 0; ii < this.drones.length; ++ii) {
      this.tickDroneEarly(this.drones[ii]);
    }
    if (this.power > 0) {
      for (let ii = 0; ii < this.drones.length; ++ii) {
        this.tickDroneActual(this.drones[ii]);
      }
    }
    for (let ii = 0; ii < this.tickables.length; ++ii) {
      this.tickTickable(this.tickables[ii]);
    }
    --this.power;
  }
}

type Floater = {
  t: number;
  t1: number;
  x: number;
  y: number;
  str: string;
};

class GameState {
  w: number;
  h: number;
  map: (MapEntry | undefined)[][];
  ld: LevelDef;
  money: number;
  sim_state!: SimState;
  ld_idx: number;
  constructor(ld_idx: number) {
    let ld = level_defs[ld_idx];
    this.ld_idx = ld_idx;
    this.ld = ld;
    let w = this.w = ld.w;
    let h = this.h = ld.h;
    this.money = ld.starting_money;

    this.map = new Array(h);
    for (let ii = 0; ii < h; ++ii) {
      this.map[ii] = new Array(w);
    }

    let basex = floor((w - BASE_SIZE) / 2);
    let basey = floor((h - BASE_SIZE) / 2);
    for (let jj = 0; jj < BASE_SIZE; ++jj) {
      for (let ii = 0; ii < BASE_SIZE; ++ii) {
        this.map[basey + jj][basex + ii] = {
          type: 'base',
          nodraw: Boolean(ii || jj),
        };
      }
    }

    view_center = [w / 2, h / 2];

    let rand = randCreate(ld.seed);
    BASE_RESOURCES.forEach((resource) => {
      for (let ii = 0; ii < ld.resources[resource]; ++ii) {
        while (true) {
          let x = rand.range(w);
          let y = rand.range(h);
          if (this.map[y][x]) {
            continue;
          }
          this.map[y][x] = {
            type: 'resource',
            resource,
          };
          break;
        }
      }
    });

    if (engine.DEBUG) {
      this.map[0][0] = {
        type: 'spawner',
        rot: 1,
      };
      this.map[0][1] = {
        type: 'rotate',
        rot: 0,
      };
      if (0) {
        this.map[2][3] = {
          type: 'storage',
          rot: 0,
        };
        this.map[3][3] = {
          type: 'storage',
          rot: 0,
        };
      } else {
        this.map[1][2] = {
          type: 'craft',
          rot: 2,
        };
        this.map[3][2] = {
          type: 'craft',
          rot: 1,
        };
      }
    }

    this.resetDay();
  }

  floaters: Floater[] = [];
  float(style: FloatStyle, x: number, y: number, str: string): void {
    this.floaters.push({
      t: 0,
      t1: FLOAT_TIME[style],
      x, y, str,
    });
  }

  resetDay(): void {
    if (this.sim_state) {
      this.money += this.sim_state.money_earned;
    }
    this.sim_state = new SimState(this, this.float.bind(this));
  }

  best_value = 0;
  calcValue(): number {
    let ss = new SimState(this, null);
    while (ss.power >= -1) {
      ss.tick();
    }
    let v = ss.money_earned;
    if (v >= this.best_value) {
      this.best_value = v;
    }
    return v;
  }

  countOf(tile_type: CellType): number {
    let r = 0;
    let { w, h, map } = this;
    for (let jj = 0; jj < h; ++jj) {
      let row = map[jj];
      for (let ii = 0; ii < w; ++ii) {
        let cell = row[ii];
        if (cell && cell.type === tile_type) {
          ++r;
        }
      }
    }
    return r;
  }

  costOf(tile_type: CellType, delta: number): number {
    let cost_calc = cost_table[tile_type];
    assert(cost_calc);
    return cost_calc[0] + cost_calc[1] * (this.countOf(tile_type) + delta - 1);
  }

  buyTile(x: number, y: number, tile_type: CellType | null, rot: number): void {
    // if (this.tutorial_state && tutorial_states[this.tutorial_state] && (
    //   !tutorial_states[this.tutorial_state].buy_validate ||
    //   !tutorial_states[this.tutorial_state].buy_validate(x, y, tile_type, rot)
    // )) {
    //   sound_manager.play('drone/place_error');
    //   floatText(x, y, 2000, 'Invalid (please follow directions)', font_style_buy);
    //   return;
    // }
    let tile = this.map[y][x];
    let dmoney = 0;
    if (!tile_type) {
      // selling
      if (tile) {
        assert(!tile.nodraw);
        let old_type = tile.type;
        let size = TILE_TYPE_SIZE[old_type] || 1;
        for (let jj = 0; jj < size; ++jj) {
          for (let ii = 0; ii < size; ++ii) {
            this.map[y + jj][x + ii] = undefined;
          }
        }
        dmoney = this.costOf(old_type, 1);
        // sound_manager.play('drone/sell');
      }
    } else {
      if (tile && tile.type === tile_type) {
        // just rotate
        tile.rot = ((tile.rot || 0) + 1) % (MAX_ROT[tile.type] || 1);
        // sound_manager.play('drone/place_rotate');
      } else {
        dmoney = -this.costOf(tile_type, 1);
        if (-dmoney > this.money) {
          // sound_manager.play('drone/place_error');
          this.float('error', x, y, `Cannot afford $${-dmoney}`);
          dmoney = 0;
        } else {
          // place new tile(s)
          // sound_manager.play('drone/place_good');
          let size = TILE_TYPE_SIZE[tile_type] || 1;
          for (let jj = 0; jj < size; ++jj) {
            for (let ii = 0; ii < size; ++ii) {
              tile = this.map[y + jj][x + ii] = {
                type: tile_type,
                rot,
                nodraw: ii !== 0 || jj !== 0,
              };
            }
          }
        }
      }
    }
    if (dmoney) {
      this.float(dmoney > 0 ? 'sell' : 'buy', x, y, `${(dmoney < 0) ? '-' : '+'}$${Math.abs(dmoney)}`);
      this.money += dmoney;
    }
    // this.saveState();
  }

}

let game_state: GameState;
let color_spawner = v4lerp(vec4(), 0.5, palette[PAL_BORDER], palette[PAL_BLACK]);

type Tool = {
  icon: string;
  type: CellType;
  tooltip: string;
};
const TOOLS: Tool[] = [{
  icon: 'drone-right',
  type: 'spawner',
  tooltip: 'Spawns a drone at the start of every day.',
}, {
  icon: 'rotate-clockwise',
  type: 'rotate',
  tooltip: 'Signals a drone to rotate when it passes over.',
}, {
  icon: 'crafter0',
  type: 'craft',
  tooltip: 'Processes resources into other resources.\n\nNote that all input' +
    ' resources must be deposited at exactly the same time.',
}, {
  icon: 'storage',
  type: 'storage',
  tooltip: 'Allows drones to deposit and pick up resources.',
}, {
  icon: 'signal-stop',
  type: 'signal-stop',
  tooltip: 'Signals a drone to stop until a nearby GO signal is activated.',
}, {
  icon: 'signal-go',
  type: 'signal-go',
  tooltip: `Signals all stopped drones within ${SIGNAL_DIST} spaces in each direction to go.`,
}];
TOOLS.forEach(function (tool, idx) {

  let cost_calc = cost_table[tool.type];
  if (cost_calc) {
    tool.tooltip += `\n\nBase Cost: $${cost_calc[0]}\nDelta Cost: $${cost_calc[1]}`;
  }

  tool.tooltip += `\n\nHotkey: ${idx + 1}`;
});

function cellFrame(type: CellType, rot: number): string {
  if (type === 'resource') {
    return 'spawn-wood';
  } else if (type === 'base') {
    return 'base';
  } else if (type === 'craft') {
    return `crafter${rot}`;
  } else if (type === 'storage') {
    return 'storage';
  } else if (type === 'spawner') {
    return `spawner-${ROT_TO_DIR[rot]}`;
  } else if (type === 'rotate') {
    return `rotate-${rot ? 'counterclockwise' : 'clockwise'}`;
  } else {
    return type;
  }
}

let selected_tool = -1;
let selected_rot = 0;
function drawHUD(): void {
  font.draw({
    x: 0, w: game_width,
    y: 0,
    align: ALIGN.HCENTER,
    text: `value: ${game_state.calcValue()}  money: ${game_state.money}`,
  });

  const TOOL_PAD = 4;
  let x = camera2d.x0();
  let y = camera2d.y0();
  let z = Z.UI;
  let w = 64;
  x += TOOL_PAD;
  y += TOOL_PAD;
  w -= TOOL_PAD * 2;
  for (let ii = 0; ii < TOOLS.length; ++ii) {
    let tool = TOOLS[ii];
    let cost = game_state.costOf(tool.type, 1);
    let icon = tool.icon;
    if (selected_tool === ii) {
      icon = cellFrame(tool.type, selected_rot);
      icon = icon.replace('spawner', 'drone');
    }
    if (button({
      x, y, z, h: BUTTON_HEIGHT,
      w,
      img: autoAtlas('main', icon),
      text: `$${cost}`,
      tooltip: tool.tooltip,
      base_name: selected_tool === ii ? 'buttonselected' : undefined,
      // disabled: cost > game_state.money,
      hotkey: KEYS['1'] + ii,
    })) {
      if (selected_tool === ii) {
        selected_rot = (selected_rot + 1) % (MAX_ROT[tool.type] || 1);
      } else {
        selected_tool = ii;
        selected_rot = selected_tool === 0 ? 2 : 0;
      }
    }
    y += BUTTON_HEIGHT + TOOL_PAD;
  }
}

function drawFloaters(dt: number): void {
  let { floaters } = game_state;
  for (let ii = floaters.length - 1; ii >= 0; --ii) {
    let floater = floaters[ii];
    floater.t += dt;
    if (floater.t >= floater.t1) {
      ridx(floaters, ii);
      continue;
    }
    font.draw({
      style: style_floater,
      alpha: min(1, (floater.t1 - floater.t) / 250),
      x: floater.x * TILE_SIZE + TILE_SIZE/2,
      y: (floater.y - floater.t / floater.t1) * TILE_SIZE,
      z: Z.FLOATERS,
      align: ALIGN.HCENTER,
      text: floater.str,
    });
  }
}

function buildMode(): void {
  let mouse_pos = mousePos();
  let x = floor(mouse_pos[0] / TILE_SIZE);
  let y = floor(mouse_pos[1] / TILE_SIZE);
  if (x < 0 || x >= game_state.w || y < 0 || y >= game_state.h) {
    return;
  }

  let tool = TOOLS[selected_tool] || null;
  let tool_w = TILE_TYPE_SIZE[tool?.type] || 1;
  let can_place = true;
  let { map } = game_state;
  let hover_cell_x = x;
  let hover_cell_y = y;
  let hover_cell: MapEntry | undefined = (map[y] || [])[x];
  if (hover_cell && hover_cell.nodraw) {
    let hover_type = hover_cell.type;
    let hover_w = TILE_TYPE_SIZE[hover_type] || 1;
    hover_cell = undefined;
    for (let jj = 0; jj < hover_w && !hover_cell; ++jj) {
      for (let ii = 0; ii < hover_w && !hover_cell; ++ii) {
        let other = (map[y - jj] || [])[x - ii];
        if (other && other.type === hover_type && !other.nodraw) {
          hover_cell_x = x - ii;
          hover_cell_y = y - jj;
          hover_cell = other;
        }
      }
    }
  }
  let can_rotate = false;
  if (hover_cell) {
    can_place = false;
    if (MAX_ROT[hover_cell.type]) {
      can_rotate = true;
    }
  }
  for (let jj = 0; jj < tool_w; ++jj) {
    for (let ii = 0; ii < tool_w; ++ii) {
      let cell = (map[y + jj] || [])[x + ii];
      if (cell && (!hover_cell || cell.type !== tool?.type)) {
        can_place = false;
      }
    }
  }

  if (x + tool_w > game_state.w ||
    y + tool_w > game_state.h
  ) {
    can_place = false;
  }

  if (tool) {
    let color: JSVec4 | Vec4 = (can_place || can_rotate) ? [1, 1, 1, 0.5] : [1, 0, 0, 0.5];
    let eff_rot = selected_rot;
    let eff_x = x;
    let eff_y = y;
    let eff_type = tool.type;
    let eff_w = tool_w;
    if (can_rotate && hover_cell) {
      eff_rot = hover_cell.rot || 0;
      eff_x = hover_cell_x;
      eff_y = hover_cell_y;
      eff_type = hover_cell.type;
      eff_w = TILE_TYPE_SIZE[eff_type] || 1;
    }
    if (eff_type === 'spawner') {
      color = (can_place || can_rotate) ? color_spawner : color;
    }
    autoAtlas('main', cellFrame(eff_type, eff_rot)).draw({
      x: eff_x * TILE_SIZE,
      y: eff_y * TILE_SIZE,
      z: Z.MAP + 2,
      w: TILE_SIZE * eff_w,
      h: TILE_SIZE * eff_w,
      color,
    });

    let mouse_up;
    if ((mouse_up = mouseUpEdge())) {
      playUISound('button_click');
      if (mouse_up.button === 1) {
        if (hover_cell) {
          for (let ii = 0; ii < TOOLS.length; ++ii) {
            if (TOOLS[ii].type === hover_cell.type) {
              selected_tool = ii;
              selected_rot = hover_cell.rot || 0;
            }
          }
        }
      } else if (mouse_up.button === 2) {
        // sell it!
        if (hover_cell) {
          for (let ii = 0; ii < TOOLS.length; ++ii) {
            if (TOOLS[ii].type === hover_cell.type) {
              selected_tool = ii;
              selected_rot = hover_cell.rot || 0;
            }
          }
          game_state.buyTile(hover_cell_x, hover_cell_y, null, 0);
        } else {
          game_state.float('error', x, y, 'Nothing to sell here');
        }
      } else {
        // place it!
        if (can_rotate) {
          game_state.buyTile(hover_cell_x, hover_cell_y, eff_type, eff_rot);
          selected_rot = hover_cell!.rot || 0;
        } else if (can_place) {
          game_state.buyTile(x, y, tool.type, selected_rot);
        } else {
          game_state.float('error', x, y, 'Placement blocked');
        }
      }
    }
  }
}

let counter = 0;
const TICK_TIME = 1000;
function statePlay(dt: number): void {

  counter += dt;
  if (counter >= TICK_TIME) {
    counter -= TICK_TIME;
    counter = min(counter, TICK_TIME - 1);
    game_state.sim_state.tick();
    if (game_state.sim_state.power < -1) {
      game_state.resetDay();
    }
  }
  let t = counter / TICK_TIME;

  drawHUD();

  let drag_ret = drag({
    x: camera2d.x0Real(),
    y: camera2d.y0Real(),
    w: camera2d.wReal(),
    h: camera2d.hReal(),
  });
  if (drag_ret) {
    view_center[0] -= drag_ret.delta[0] / TILE_SIZE;
    view_center[1] -= drag_ret.delta[1] / TILE_SIZE;
  }
  camera2d.push();
  let x0 = view_center[0] * TILE_SIZE - game_width / 2;
  let y0 = view_center[1] * TILE_SIZE - game_height / 2;
  camera2d.set(x0, y0, x0 + game_width, y0 + game_height);
  let { map, w, h, sim_state } = game_state;
  let { drones, transfers, sim_map } = sim_state;
  let z = Z.MAP;
  let bg = autoAtlas('main', 'bg');

  function isTransferTo(x: number, y: number): 'from' | 'within' | null {
    for (let ii = 0; ii < transfers.length; ++ii) {
      let elem = transfers[ii];
      if ((elem[0] === 'from' || elem[0] === 'within') && elem[4] === x && elem[5] === y) {
        return elem[0];
      }
    }
    return null;
  }

  for (let yy = 0; yy < h; ++yy) {
    let row = map[yy];
    let sim_row = sim_map[yy];
    for (let xx = 0; xx < w; ++xx) {
      let tile = row[xx];
      bg.draw({
        x: xx * TILE_SIZE,
        y: yy * TILE_SIZE,
        z: z - 0.2,
        w: TILE_SIZE,
        h: TILE_SIZE,
      });
      if (!tile) {
        continue;
      }
      if (tile.nodraw) {
        continue;
      }
      let ww = TILE_TYPE_SIZE[tile.type] || 1;
      let color: Vec4 | undefined;
      let zz = z;

      let frame = cellFrame(tile.type, tile.rot!);
      if (tile.type === 'resource') {
        frame = `spawn-${tile.resource!}`;
      } else if (tile.type === 'spawner') {
        color = color_spawner;
        zz -= 0.1;
      }
      autoAtlas('main', frame).draw({
        x: xx * TILE_SIZE,
        y: yy * TILE_SIZE,
        z: zz,
        w: TILE_SIZE * ww,
        h: TILE_SIZE * ww,
        color,
      });

      let sim_tile = sim_row[xx];
      if (sim_tile) {
        if (sim_tile.contents) {
          if (isTransferTo(xx, yy)) {
            // hide
          } else {
            autoAtlas('main', `resource-${sim_tile.contents}`).draw({
              x: xx * TILE_SIZE,
              y: yy * TILE_SIZE,
              z: zz + 0.1,
              w: TILE_SIZE,
              h: TILE_SIZE,
              color,
            });
          }
        } else if (tile.type === 'craft') {
          for (let ii = 0; ii < sim_tile.multi_contents.length; ++ii) {
            let content = sim_tile.multi_contents[ii];
            if (content) {
              let coords = craft_contents_coords[(ii + (tile.rot || 0)) % 4];
              let x2 = xx + coords[0];
              let y2 = yy + coords[1];
              let trans = isTransferTo(x2, y2);
              if (
                trans === 'from' ||
                trans === 'within' && t < 0.5
              ) {
                // hide
              } else {
                autoAtlas('main', `resource-${content}`).draw({
                  x: x2 * TILE_SIZE,
                  y: y2 * TILE_SIZE,
                  z: zz + 0.1,
                  w: TILE_SIZE,
                  h: TILE_SIZE,
                  color,
                });
              }
            }
          }
        }
      }
    }
  }
  z++;

  // draw drones
  let progress = t;
  if (sim_state.power < 0) {
    progress = 0;
  }
  // [0,0.5,1] -> [0,1,1]
  let blend = easeInOut(
    clamp(2 * progress, 0, 1),
    2
  );
  // [0,bump_time,bump_time*2,1] = [0,0.3,0,0];
  let bump_time = 0.2;
  let bump_blend = 0.3 * easeIn(max(0, 1 - 1/bump_time * abs(bump_time - progress)), 2);

  for (let ii = 0; ii < drones.length; ++ii) {
    let drone = drones[ii];
    let { x, y, rot, contents, last_x, last_y, last_rot, last_contents, gain_resource_tick } = drone;

    if (x !== last_x || y !== last_y) {
      x = lerp(blend, last_x, x);
      y = lerp(blend, last_y, y);
    } else if (!sim_state.isDay0()) {
      let target_x = x + DX[rot];
      let target_y = y + DY[rot];
      x = lerp(bump_blend, x, target_x);
      y = lerp(bump_blend, y, target_y);
    }
    if (progress < 0.75) {
      rot = last_rot;
    }
    if (blend < 1) {
      contents = last_contents;
    }

    let frame = `drone-${ROT_TO_DIR[rot]}`;
    if (sim_state.power < 0) {
      frame = 'drone-sleep';
    }
    autoAtlas('main', frame).draw({
      x: x * TILE_SIZE,
      y: y * TILE_SIZE,
      z,
      w: TILE_SIZE,
      h: TILE_SIZE,
    });

    if (contents) {
      if (gain_resource_tick === sim_state.tick_id && !last_contents) {
        // don't draw resource
      } else {
        autoAtlas('main', `resource-${contents}`).draw({
          x: x * TILE_SIZE,
          y: y * TILE_SIZE,
          z: z + 0.1,
          w: TILE_SIZE,
          h: TILE_SIZE,
        });
      }
    }
  }

  // draw resource transfers
  // [0,0.5,1] -> [0,0,1]
  let blend_inout = easeInOut(
    clamp(2 * progress - 1, 0, 1),
    2
  );
  for (let ii = 0; ii < transfers.length; ++ii) {
    let trans = transfers[ii];
    let [mode, res, x, y, to_x, to_y] = trans;
    if (mode === 'within') {
      if (blend === 1) {
        continue;
      }
      x = lerp(blend, x, to_x);
      y = lerp(blend, y, to_y);
    } else { // to/from
      if (blend < 1 && (mode !== 'pickup' || isTransferTo(x, y))) {
        continue;
      }
      x = lerp(blend_inout, x, to_x);
      y = lerp(blend_inout, y, to_y);
    }
    autoAtlas('main', `resource-${res}`).draw({
      x: x * TILE_SIZE,
      y: y * TILE_SIZE,
      z: z + 0.1,
      w: TILE_SIZE,
      h: TILE_SIZE,
    });
  }

  drawFloaters(dt);

  buildMode();

  camera2d.pop();
}

function playInit(): void {
  engine.setState(statePlay);
  counter = 0;
  selected_tool = engine.DEBUG ? 0 : -1;
  selected_rot = engine.DEBUG ? 2 : 0;
  game_state = new GameState(engine.DEBUG ? 1 : 0);
}

export function main(): void {
  if (platformParameterGet('reload_updates') && engine.DEBUG) {
    // Enable auto-reload, etc
    netInit({ engine });
  }

  const font_info_04b03x2 = require('./img/font/04b03_8x2.json');
  const font_info_04b03x1 = require('./img/font/04b03_8x1.json');
  const font_info_palanquin32 = require('./img/font/palanquin32.json');
  let pixely = 'on';
  let font_def;
  let ui_sprites;
  let pixel_perfect = 0;
  if (pixely === 'strict') {
    font_def = { info: font_info_04b03x1, texture: 'font/04b03_8x1' };
    ui_sprites = spriteSetGet('pixely');
    pixel_perfect = 1;
  } else if (pixely && pixely !== 'off') {
    font_def = { info: font_info_04b03x2, texture: 'font/04b03_8x2' };
    ui_sprites = spriteSetGet('pixely');
  } else {
    font_def = { info: font_info_palanquin32, texture: 'font/palanquin32' };
  }

  if (!engine.startup({
    game_width,
    game_height,
    pixely,
    font: font_def,
    viewport_postprocess: false,
    antialias: false,
    ui_sprites: {
      ...ui_sprites,
      color_set_shades: [1,1,1],
      buttonselected_regular: { atlas: 'pixely', name: 'button_selected' },
      buttonselected_down: { atlas: 'pixely', name: 'button_down' },
      buttonselected_rollover: { atlas: 'pixely', name: 'button_rollover' },
      buttonselected_disabled: { atlas: 'pixely', name: 'button_disabled' },
    },
    pixel_perfect,
  })) {
    return;
  }
  font = uiGetFont();

  // Perfect sizes for pixely modes
  scaleSizes(13 / 32);
  setFontHeight(FONT_HEIGHT);
  setButtonHeight(BUTTON_HEIGHT);
  setFontStyles(
    fontStyleColored(null, palette_font[PAL_BLACK]),
    fontStyleColored(null, palette_font[PAL_BLACK]),
    fontStyleColored(null, palette_font[PAL_BLACK]),
    fontStyleColored(null, palette_font[PAL_BLACK]),
  );

  gl.clearColor(clear_color[0], clear_color[1], clear_color[2], clear_color[3]);
  v4copy(engine.border_clear_color, clear_color);
  v4copy(engine.border_color, clear_color);

  init();

  playInit();
}
