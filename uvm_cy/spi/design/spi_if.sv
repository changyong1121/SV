interface spi_master_controller_if;

	logic 		clk_tb;      // System clock
	logic 		rst_n_tb;    // Active-low reset
	logic 		start_tb;    // Start transmission
  	logic [7:0]	tx_data_tb;  // Data to transmit
 	logic [7:0]  	rx_data_tb;  // Received data
	logic        	busy_tb;     // Transmission in progress
	logic        	done_tb;     // Transmission complete
    
    // SPI interface
 	logic        sclk_tb;       // SPI clock
 	logic        mosi_tb;       // Master out, slave in
 	logic        miso_tb;       // Master in, slave out
 	logic        cs_n_tb;       // Chip select (active low)


//modport for monitor : read only
	modport mon_mp(	
		input clk_tb,rst_n_tb,start_tb,tx_data_tb,rx_data_tb,busy_tb,done_tb,sclk_tb,mosi_tb,miso_tb,cs_n_tb
	);

//modport for driver 
//maybe got error need review
	modport drv_mp(
		input clk_tb,busy_tb,done_tb, 
		output rst_n_tb,start_tb,tx_data_tb,rx_data_tb,sclk_tb,mosi_tb,miso_tb,cs_n_tb   	
	
	);



endinterface
