`include "spi_if.sv"
`include "spi.sv"

module spi_tb;
	//import uvm_pkg::*;
	`include "uvm_macros.svh"
 // $time is a built-in system function
  initial $display(">>>>>>>> SIM TIME START: %0t", $time);
  final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

   spi_master_controller_if spi_if();

  spi #(.CLK_DIV(4)) dut(
            .clk    (spi_if.clk_tb    ),      // System clock
            .rst_n  (spi_if.rst_n_tb  ),    // Active-low reset
            .start  (spi_if.start_tb  ),    // Start transmission
            .tx_data(spi_if.tx_data_tb),  // Data to transmit
            .rx_data(spi_if.rx_data_tb),  // Received data
            .busy   (spi_if.busy_tb),     // Transmission in progress
            .done   (spi_if.done_tb),     // Transmission complete
    // SPI interface
            .sclk(spi_if.sclk_tb),     // SPI clock
            .mosi(spi_if.mosi_tb),     // Master out, slave in
            .miso(spi_if.miso_tb),     // Master in, slave out
            .cs_n(spi_if.cs_n_tb)      // Chip select (active low)
	);

initial begin
	spi_if.clk_tb = 0;
	forever #5 spi_if.clk_tb = ~spi_if.clk_tb;
	
end	

initial begin
//	uvm_config_db#(virtual spi_master_controller_if )::set(null, "uvm_test_top.env.aft.drv", "vif", spi_vif);	//uvm_config_db#(virtual spi_master_controller_if )::set(null, "uvm_test_top.env.aft.drv", "vif", spi_vif)
	uvm_config_db#(virtual spi_master_controller_if )::set(null, "*", "vif", spi_if);
 	run_test("spi_test");

end

initial begin 
    $fsdbDumpfile("spi_sim.fsdb");
    $fsdbDumpSVA(0, spi_tb);
    $fsdbDumpvars(0, spi_tb);

end




/////////////////////////////////////content1/////////////////////////////
   // Constants
    bit [7:0] SLAVE_RESET_RESPONSE = 8'hB9;
    int slave_reset_response = SLAVE_RESET_RESPONSE;
    
    // Simple SPI slave model for testing
    logic [7:0] slave_rx_data;
    logic [7:0] slave_tx_data;
    logic [3:0] idle_counter;
    
    always @(posedge spi_if.sclk_tb or negedge spi_if.rst_n_tb or posedge spi_if.cs_n_tb) begin
        if (!spi_if.rst_n_tb) begin
            slave_rx_data <= 8'h00;
            spi_if.miso_tb <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
	else if (spi_if.cs_n_tb) begin
            spi_if.miso_tb <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;

	    `uvm_info("SLV-RLD", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                               slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
	else begin
                // Shift in MOSI on rising edge
                slave_rx_data <= {slave_rx_data[6:0], spi_if.mosi_tb};

                // Update MISO immediately for next bit
                spi_if.miso_tb <= slave_tx_data[7];
                slave_tx_data <= {slave_tx_data[6:0], 1'b0};

		`uvm_info("SLV", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                           slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
    end

    always @(posedge spi_if.clk_tb or negedge spi_if.rst_n_tb) begin
        if (!spi_if.rst_n_tb) begin
            idle_counter <= 5'd0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
        else if (spi_if.cs_n_tb) begin  // SPI idle (cs_n=1)
            if (idle_counter < 5'd7) begin
                slave_tx_data <= 8'h00;  // Drive 0 for 8 cycles
                idle_counter <= idle_counter + 1;
            end
            else begin
                slave_tx_data <= SLAVE_RESET_RESPONSE;  // Revert to default
            end
        end
        else begin  // SPI active (cs_n=0)
            idle_counter <= 5'd0;  // Reset counter
        end
    end


////////////////////////////////end content1/////////////

endmodule
