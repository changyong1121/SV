/*
class spi_scb extends uvm_scoreboard;
    `uvm_component_utils(spi_scb)
  
    // Use implementation port to receive transactions
    uvm_analysis_imp #(spi_tran, spi_scb) scb_imp;
  
    int passed_count = 0;
    int failed_count = 0;
    int tran_count;
    int tran_index;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        tran_index = 1;
        scb_imp = new("scb_imp", this);
    endfunction

    function void write(spi_tran tr_dut);

    endfunction

    function void report_phase(uvm_phase phase);
        `uvm_info("SCOREBOARD", "Test Complete.", UVM_NONE) 
//Passed: %0d Failed: %0d", passed_count, failed_count), UVM_NONE)
    endfunction
endclass

*/

class spi_scb extends uvm_scoreboard;

  // Analysis port to receive sequence items
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp;

  // Expected response pattern (slave sends 0xB9, then shifts 0)
  bit [7:0] expected_tx_response = 8'hB9;

  // Tracking and statistics
  int passed_count = 0;
  int failed_count = 0;
  int tran_count   = 0;
  int tran_index   = 0;
  int slave_reset_response;
  `uvm_component_utils(spi_scb)

  function new(string name, uvm_component parent);
    super.new(name, parent);
    scb_imp = new("scb_imp", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(int)::get(this, "", "slave_reset_response", slave_reset_response))
        `uvm_fatal("CFG", "Failed to get 'slave_reset_response' from config DB");
    expected_tx_response = slave_reset_response;
  endfunction

  function void write(spi_tran tr_dut);
    bit [7:0] expected_rx;

    tran_index++;
    tran_count++;

    expected_rx = expected_tx_response;
    expected_tx_response = {expected_tx_response[6:0], 1'b0};  // Update for next

    if (tr_dut.rx_data !== expected_rx) begin
      `uvm_error("SB", $sformatf("Transaction %0d FAILED: Expected 0x%2h, Got 0x%2h",
                                 tran_index, expected_rx, tr_dut.rx_data))
      failed_count++;
    end else begin
      `uvm_info("SB", $sformatf("Transaction %0d PASSED: RX = 0x%2h",
                                tran_index, tr_dut.rx_data), UVM_LOW)
      passed_count++;
    end
  endfunction

  // Optionally print summary at end of simulation
  function void report_phase(uvm_phase phase);
    `uvm_info("SB-REPORT", $sformatf("Total Transactions: %0d", tran_count), UVM_NONE)
    `uvm_info("SB-REPORT", $sformatf("Passed: %0d", passed_count), UVM_NONE)
    `uvm_info("SB-REPORT", $sformatf("Failed: %0d", failed_count), UVM_NONE)

    if (failed_count > 0)
      `uvm_error("SB", "Some transactions failed. See log.")
    else
      `uvm_info("SB", "All transactions passed successfully.", UVM_NONE)
  endfunction

endclass

