/* eslint n/global-require:off */
// eslint-disable-next-line import/order
const local_storage = require('glov/client/local_storage');
local_storage.setStoragePrefix('ld59'); // Before requiring anything else that might load from this

import assert from 'assert';
import { autoAtlas } from 'glov/client/autoatlas';
import * as camera2d from 'glov/client/camera2d';
import { platformParameterGet } from 'glov/client/client_config';
import * as engine from 'glov/client/engine';
import { drag } from 'glov/client/input';
import { netInit } from 'glov/client/net';
import { spriteSetGet } from 'glov/client/sprite_sets';
import {
  scaleSizes,
  setFontHeight,
} from 'glov/client/ui';
import { randCreate } from 'glov/common/rand_alea';
import { JSVec2, v4copy, Vec4, vec4 } from 'glov/common/vmath';
import { PAL_BORDER, palette } from './palette';

const { floor } = Math;

window.Z = window.Z || {};
Z.BACKGROUND = 1;
Z.SPRITES = 10;
Z.MAP = 10;

// Virtual viewport for our game logic
const game_width = 384;
const game_height = 256;

const TILE_SIZE = 15;

function init(): void {
  // anything?
  autoAtlas('main', 'base');
}

const clear_color = palette[PAL_BORDER];

const RESOURCES = ['wood', 'stone', 'fruit'] as const;
type ResourceType = typeof RESOURCES[number];
type LevelDef = {
  w: number;
  h: number;
  starting_power: number;
  starting_money: number;
  resources: Record<ResourceType, number>;
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
}];

const ROT_TO_DIR = [
  'up',
  'right',
  'down',
  'left',
] as const;
const DX = [0, 1, 0, -1];
const DY = [-1, 0, 1, 0];

type CellType = 'base' | 'craft' | 'resource' | 'spawner' | 'rotate' | 'signal-stop' | 'signal-go' | 'storage';
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
  x: number;
  y: number;
  rot: number;
  contents: null | ResourceType;
  tick_id: number;
  thinking: boolean;
  uid: number;
  gain_resource_tick?: number;
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

function resourceValue(res: ResourceType): number {
  return 100;
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
  constructor(parent: GameState) {
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
            x: ii,
            y: jj,
            rot: cell.rot || 0,
            contents: null,
            tick_id: 0,
            thinking: false,
            uid: ++this.last_uid,
          };
          drones.push(drone);
          this.drone_map[jj][ii] = drone;
        } else if (cell.type === 'base' || cell.type === 'resource' ||
          cell.type === 'storage' || cell.type === 'craft'
        ) {
          let tickable = {
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
    return this.drone_map[x][y] || null;
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
        // this.resource_transfers.push([tile.resource, ticker.x, ticker.y, target_x, target_y]);
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
          // floatText((ticker.x + base_contents_coords[ii][0]), (ticker.y + base_contents_coords[ii][1]),
          //   FLOATER_TIME_BASE_SALE, `${resource_types[res].type}: +$${resource_value}`, font_style_sale);
          // playUISound('sell');
        }
      }
    }

    if (this.power <= 0) {
      return;
    }
    for (let jj = 0; jj < base_slurp_coords.length; ++jj) {
      let target_contents = base_slurp_coords[jj][2];
      if (ticker.multi_contents && ticker.multi_contents[target_contents]) {
        // already full
        continue;
      }
      let target_x = ticker.x + base_slurp_coords[jj][0];
      let target_y = ticker.y + base_slurp_coords[jj][1];
      let target_actor = this.getDrone(target_x, target_y);
      if (!target_actor || target_actor.gain_resource_tick === this.tick_id) {
        continue;
      }
      if (target_actor.contents) {
        ticker.multi_contents = ticker.multi_contents || [];
        ticker.multi_contents[target_contents] = target_actor.contents;
        // this.resource_transfers.push([
        //   target_actor.carrying, target_x, target_y,
        //   ticker.x + base_contents_coords[target_contents][0], ticker.y + base_contents_coords[target_contents][1]
        // ]);
        target_actor.contents = null;
        target_actor.gain_resource_tick = this.tick_id;
        // playUISound('dropoff');
      }
    }
  }
  tickCrafter(ticker: SimMapEntry): void {
    // TODO
  }
  tickStorage(ticker: SimMapEntry): void {
    // TODO
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
  tick(): void {
    ++this.tick_id;
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

class GameState {
  w: number;
  h: number;
  map: (MapEntry | undefined)[][];
  ld: LevelDef;
  money: number;
  sim_state: SimState;
  constructor(ld: LevelDef) {
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
    RESOURCES.forEach((resource) => {
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

    // debug
    this.map[0][4] = {
      type: 'spawner',
      rot: 2,
    };

    this.sim_state = new SimState(this);
  }
}

let game_state: GameState;
let color_spawner = vec4(1, 1, 1, 0.5);

function statePlay(dt: number): void {

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
  let { map, w, h } = game_state;
  let z = Z.MAP;
  let bg = autoAtlas('main', 'bg');
  for (let yy = 0; yy < h; ++yy) {
    let row = map[yy];
    for (let xx = 0; xx < w; ++xx) {
      let tile = row[xx];
      bg.draw({
        x: xx * TILE_SIZE,
        y: yy * TILE_SIZE,
        z: z - 0.2,
        w: TILE_SIZE,
        h: TILE_SIZE,
      });
      let ww = 1;
      if (!tile) {
        continue;
      }
      if (tile.nodraw) {
        continue;
      }
      let frame;
      let color: Vec4 | undefined;
      let zz = z;
      if (tile.type === 'resource') {
        frame = `spawn-${tile.resource!}`;
      } else if (tile.type === 'base') {
        frame = 'base';
        ww = 3;
      } else if (tile.type === 'craft') {
        frame = `crafter${tile.rot}`;
        ww = 2;
      } else if (tile.type === 'storage') {
        frame = 'storage';
      } else if (tile.type === 'spawner') {
        frame = `spawner-${ROT_TO_DIR[tile.rot!]}`;
        color = color_spawner;
        zz -= 0.1;
      } else if (tile.type === 'rotate') {
        frame = `rotate-${tile.rot ? 'counterclockwise' : 'clockwise'}`;
      } else {
        frame = tile.type;
      }
      autoAtlas('main', frame).draw({
        x: xx * TILE_SIZE,
        y: yy * TILE_SIZE,
        z: zz,
        w: TILE_SIZE * ww,
        h: TILE_SIZE * ww,
        color,
      });
    }
  }
  camera2d.pop();
}

function playInit(): void {
  engine.setState(statePlay);
  game_state = new GameState(level_defs[0]);
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
    ui_sprites,
    pixel_perfect,
  })) {
    return;
  }
  // let font = engine.font;

  // Perfect sizes for pixely modes
  scaleSizes(13 / 32);
  setFontHeight(8);

  gl.clearColor(clear_color[0], clear_color[1], clear_color[2], clear_color[3]);
  v4copy(engine.border_clear_color, clear_color);
  v4copy(engine.border_color, clear_color);

  init();

  playInit();
}
