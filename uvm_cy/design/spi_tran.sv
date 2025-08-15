class spi_tran extends uvm_sequence_item;

 	bit clk;

      bit       rst_n;    // Active-low reset
      rand bit       start;    // Start transmission
      rand bit [7:0]  tx_data;  // Data to transmit
      bit[7:0]  rx_data;  // Received data
      bit       busy;     // Transmission in progress
      bit       done;     // Transmission complete
    
    // SPI interface
      bit      sclk;     // SPI clock
      bit      mosi;     // Master out, slave in
      bit      miso;     // Master in, slave out
      bit      cs_n;     // Chip select (active low)

      
      int tran_count;
      int tran_index;

    // === UVM registration ===
	`uvm_object_utils(spi_tran)

    // === Constructor ===
	function new (string name = "spi_tran");
	 super.new(name);
	endfunction
/*
    // === Optional: Randomization constraints ===
  constraint valid_tx_data {
    tx_data inside {[8'h10:8'hF0]};  // Constrain to avoid special/reserved values
  }

*/

endclass








