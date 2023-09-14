from fridge_utils import *
import pandas as pd

if __name__ == '__main__':  
    
    # parallel processes to run
    par = 4
    
    print('... Running 3-Gate complete tests: ...')
    print('... acyclic ...')
    run_test_inv_2f_all(get_inv_3G_complete_acyclic, filename='data/_acyc_3g_complete.csv',       start_fi0 = 0, upto=255, processes=par, opt=True, display_progress = True)
    print('... oneshot-style cyclic ...')
    run_test_inv_2f_all(get_inv_3G_complete_cyclic,  filename='data/_cyc_3g_complete_molec.csv',  start_fi0 = 0, upto=255, processes=par, opt=True, display_progress = True, riedel=False)

    print('... Running 4-Gate complete tests: ...')
    print('... acyclic ...')
    run_test_inv_2f_all(get_inv_4G_complete_acyclic, filename='data/_acyc_4g_complete.csv',       start_fi0 = 0, upto=255, processes=par, opt=True, display_progress = True)
    print('... oneshot-style cyclic ...')
    run_test_inv_2f_all(get_inv_4G_complete_cyclic,  filename='data/_cyc_4g_complete_molec.csv',  start_fi0 = 0, upto=255, processes=par, opt=True, display_progress = True, riedel=False)

    print('... Running 19-Gate 27-Wire tests: ...')
    inventory_test_all_funcs(get_inv_19g_27w, filename='data/_19g_27w_4bit.csv', start_i = 0, processes=par, N_XVARS = 4, save_chunks = 8, verif=False)
    cdf_plot_time('data/_19g_27w_4bit.csv', '19g 27w', 4)
    
    print('... Running 5-Gate 12-Wire tests: ...')
    inventory_test_all_funcs(get_inv_5g_12w, filename='data/_5g_12w_4bit.csv', start_i = 0, processes=par, N_XVARS = 4, save_chunks = 512, verif=False)
    inventory_test_all_funcs(get_inv_5g_12w, filename='data/_5g_12w_3bit.csv', start_i = 0, processes=par, N_XVARS = 3, save_chunks = 512, verif=False)
