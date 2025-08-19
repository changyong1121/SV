interface spi_slv_if(input logic clk);
  
  // Inputs from master
  logic rst_n;
  logic sclk;
  logic cs_n;
  logic mosi;


  // Outputs from slave
  logic miso;

  // Internal signals for observation
  logic [7:0] slave_rx_data;
  logic [7:0] slave_tx_data;

  // Optional modport for scoreboard access
  modport mon_cb(
    input slave_rx_data, slave_tx_data
  );

endinterface

