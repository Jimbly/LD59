import { vec4ColorFromIntColor } from 'glov/client/font';
import { vec4 } from 'glov/common/vmath';

export const palette_font = [
  0xffffffFF,
  0xffd19dFF,
  0xaeb5bdFF,
  0x4d80c9FF,
  0xe93841FF,
  0x100820FF,
  0x511e43FF,
  0x054494FF,
  0xf1892dFF,
  0x823e2cFF,
  0xffa9a9FF,
  0x5ae150FF,
  0xffe947FF,
  0x7d3ebfFF,
  0xeb6c82FF,
  0x1e8a4cFF,
];

export const palette = palette_font.map((hex) => {
  return vec4ColorFromIntColor(vec4(), hex);
});

export const PAL_BLUE = 7;
export const PAL_GREEN = 11;
export const PAL_ORANGE = 8;
export const PAL_YELLOW = 12;
export const PAL_RED = 4;
export const PAL_BLACK = 5;
export const PAL_WHITE = 0;
export const PAL_GREY = 2;
export const PAL_BORDER = 6;
