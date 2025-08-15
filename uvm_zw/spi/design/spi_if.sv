interface spi_if;
    logic [7:0] tx_data;     // Input to DUT (driven by testbench)
    logic start;      
    logic clk;    
    logic rst_n;   
    logic [7:0] rx_data;   
    logic busy;
    logic done;
    logic        sclk;
    logic        mosi;
    logic        miso;
    logic        cs_n;



    clocking drv_cb @(posedge clk);
        default input #1step output #1;
        output tx_data, start;
        input rx_data, busy, done;
    endclocking

    clocking mon_cb @(posedge clk);
        default input #1step;
        input tx_data, start,rx_data, busy, done;
    endclocking

endinterface

