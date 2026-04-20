module.exports = function (config) {

  config.extra_index = [{
    name: 'itch',
    defines: {
      ...config.default_defines,
      PLATFORM: 'itch',
    },
    zip: true,
    wrapper: 'itchlaunch.html',
  }];
  config.extra_client_html = ['client/itchlaunch.html'];

  config.extra_index = [{
    name: 'wavedash',
    defines: {
      ...config.default_defines,
      PLATFORM: 'wavedash',
    },
    zip: true,
  }];
};
