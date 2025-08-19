`include "spi_if.sv"
`include "spi_slv_if.sv"
`include "spi.sv"

module spi_tb;
    //import uvm_pkg::*;
    `include "uvm_macros.svh"

    // $time is a built-in system function
    initial $display(">>>>>>>> SIM TIME START: %0t", $time);
    final   $display(">>>>>>>> SIM TIME END  : %0t", $time);


    spi_if spi_if();
    spi_slv_if spi_slv_if(spi_if.clk);

    spi #(.CLK_DIV(4)) dut(
    .clk(spi_if.clk),
    .rst_n(spi_if.rst_n),
    .start(spi_if.start),
    .tx_data(spi_if.tx_data),
    .rx_data(spi_if.rx_data),
    .busy(spi_if.busy),
    .done(spi_if.done),
    .sclk(spi_if.sclk),
    .mosi(spi_if.mosi),
    .miso(spi_if.miso),
    .cs_n(spi_if.cs_n)
    );

    //spi_slv_if spi_slv_if(.*);
    

    bit [7:0] SLAVE_RESET_RESPONSE = 8'hB9;
    int slave_reset_response = SLAVE_RESET_RESPONSE;
    
    // Simple SPI slave model for testing
    //logic [7:0] slave_rx_data;
    //logic [7:0] slave_tx_data;
    logic [3:0] idle_counter;
    
    always @(posedge spi_if.sclk or negedge spi_if.rst_n or posedge spi_if.cs_n) begin
        if (!spi_if.rst_n) begin
            spi_slv_if.slave_rx_data <= 8'h00;
            spi_if.miso <= 1'b0;
            spi_slv_if.slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
	else if (spi_if.cs_n) begin
            spi_if.miso <= 1'b0;
            spi_slv_if.slave_tx_data <= SLAVE_RESET_RESPONSE;

	    `uvm_info("SLV-RLD", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                               spi_slv_if.slave_rx_data, spi_slv_if.slave_rx_data, spi_slv_if.slave_tx_data, spi_slv_if.slave_tx_data), UVM_MEDIUM)
        end
	else begin
                // Shift in MOSI on rising edge
                spi_slv_if.slave_rx_data <= {spi_slv_if.slave_rx_data[6:0], spi_if.mosi};

                // Update MISO immediately for next bit
                spi_if.miso <= spi_slv_if.slave_tx_data[7];
                spi_slv_if.slave_tx_data <= {spi_slv_if.slave_tx_data[6:0], 1'b0};

		`uvm_info("SLV", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                           spi_slv_if.slave_rx_data, spi_slv_if.slave_rx_data, spi_slv_if.slave_tx_data, spi_slv_if.slave_tx_data), UVM_MEDIUM)
        end
    end

    always @(posedge spi_if.clk or negedge spi_if.rst_n) begin
        if (!spi_if.rst_n) begin
            idle_counter <= 5'd0;
            spi_slv_if.slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
        else if (spi_if.cs_n) begin  // SPI idle (cs_n=1)
            if (idle_counter < 5'd7) begin
                spi_slv_if.slave_tx_data <= 8'h00;  // Drive 0 for 8 cycles
                idle_counter <= idle_counter + 1;
            end
            else begin
                spi_slv_if.slave_tx_data <= SLAVE_RESET_RESPONSE;  // Revert to default
            end
        end
        else begin  // SPI active (cs_n=0)
            idle_counter <= 5'd0;  // Reset counter
        end
    end
 
    initial begin
        spi_if.clk = 0;
        spi_if.start = 0;
        spi_if.tx_data = 0;
        spi_if.rst_n = 0;
        #50;
        spi_if.rst_n = 1;
 
        forever #5 spi_if.clk = ~spi_if.clk;
    end

    initial begin
        uvm_config_db#(virtual spi_if)::set(null, "*", "vif", spi_if);
        uvm_config_db#(virtual spi_slv_if)::set(null, "*", "slv_vif", spi_slv_if);
        uvm_config_db#(int)::set(null, "*", "slave_reset_response", slave_reset_response);
               
        run_test("spi_test");
    end

    initial begin
        $fsdbDumpfile("spi_sim.fsdb");
        $fsdbDumpSVA(0, spi_tb);
        $fsdbDumpvars(0, spi_tb);
    end

     
endmodule

