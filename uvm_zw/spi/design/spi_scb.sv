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
  
  virtual spi_slv_if spi_slv_if;
 

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(int)::get(this, "", "slave_reset_response", slave_reset_response)) begin
        `uvm_fatal("CFG", "Failed to get 'slave_reset_response' from config DB");
    end

    if (!uvm_config_db#(virtual spi_slv_if)::get(this, "", "slv_vif", spi_slv_if)) begin
        `uvm_fatal("SB", "Failed to get slave virtual interface");
    end

       expected_tx_response = slave_reset_response;
  endfunction

  function void write(spi_tran tr_dut);
    bit [7:0] expected_slv_rx;
    bit [7:0] slv_rx;
    bit [7:0] current_tx_data;
    int shift_count = 0;  // Starts at 1 (tx_data[7] only)
    

/*
    current_tx_data = tr_dut.tx_data;
    shift_count = 0;
    `uvm_info("SB", $sformatf("Start asserted — new transfer: tx_data = 0x%0h", current_tx_data), UVM_MEDIUM)

    expected_slv_rx = (expected_slv_rx << 1) | current_tx_data[7 - shift_count];
    slv_rx = spi_slv_if.slave_rx_data;

        if (slv_rx !== expected_slv_rx) begin
            `uvm_error("SB", $sformatf(
                "Mismatch: Expected = 0x%0b, Got = 0x%0b",
                expected_slv_rx, slv_rx))
            failed_count++;
        end else begin
            `uvm_info("SB", $sformatf(
                "PASS: Expected = 0x%0b, Got = 0x%0b",
                expected_slv_rx, slv_rx), UVM_LOW)
            passed_count++;
        end
        
        shift_count++;

    if (shift_count == 8) begin
        shift_count = 0;
    end

    tran_count++;
    tran_index++;
endfunction
*/
//function void write(spi_tran tr_dut);
    if (tr_dut.start) begin
        current_tx_data = tr_dut.tx_data;
        shift_count = 0;
        expected_slv_rx = 0;  // reset accumulation only on new transfer
        `uvm_info("SB", $sformatf("Start asserted: tx_data = 0x%0h", current_tx_data), UVM_MEDIUM)
    end

    // Shift in one bit per cycle
    bit expected_bit = current_tx_data[7 - shift_count];
    expected_slv_rx = (expected_slv_rx << 1) | expected_bit;

    bit [7:0] slv_rx = spi_slv_if.slave_rx_data;

    `uvm_info("SB", $sformatf("Cycle %0d: expected_bit = %0b, expected_slv_rx = 0x%0b, slave_rx = 0x%0b",
                 shift_count, expected_bit, expected_slv_rx, slv_rx), UVM_LOW)

    if (expected_slv_rx !== slv_rx) begin
        `uvm_error("SB", $sformatf("Mismatch at bit %0d: expected = 0x%0b, got = 0x%0b",
                                   shift_count, expected_slv_rx, slv_rx))
        failed_count++;
    end else begin
        `uvm_info("SB", $sformatf("PASS at bit %0d: expected = 0x%0b, got = 0x%0b",
                                  shift_count, expected_slv_rx, slv_rx), UVM_LOW)
        passed_count++;
    end

    shift_count++;

    if (shift_count == 8)
        shift_count = 0;

    tran_index++;
    tran_count++;
endfunction

endclass

