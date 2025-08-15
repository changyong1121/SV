import uvm_pkg::*;

class spi_tran extends uvm_sequence_item;

    randc bit [7:0]  tx_data;  // Data to transmit
    rand bit         start;    // Start transmission
    bit              rst_n;    // Active-low reset
    bit       [7:0]  rx_data;  // Received data
    bit              busy;     // Transmission in progress
    bit              done;     // Transmission complete
    bit              sclk;  
    bit              mosi;     
    bit              miso; 
    bit              cs_n;  
    int seq_count;
    int seq_index;
    int tran_count;
    int tran_index;
    string seq_type;
    string tran_type;

    `uvm_object_utils(spi_tran)

    function new(string name = "spi_tran");
        super.new(name);
    endfunction
endclass
